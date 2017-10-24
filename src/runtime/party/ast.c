#include "party.h"
#include <assert.h>
#include "list.c"

// All Expression combinators have always a source (ParT) and
// a transformation function (lambda). Based on the tag, cast
// the ExprValue_t to the appropriate combinator expression to
// access 'hidden' fields. You can think of this struct as the
// parent of any other more complex expression, i.e.
//
//                  ast_expr_t (>>, join, extract, each, distinct)
//                        /\
//                       /  \
//   (reduce) ast_reduce_t   ast_two_par_tsource_t (intersection, zip)
//

// NOTE: Based on the rules from the paper:
//
// { v }_read >>_lin e ---> { e(v) }_lin
//
// and because { v_lin }_read is not allowed, we can use restrict keyword
// if the >>_lin is specified, making `e` always safe to restrictify.
//
// If the compiler detects that >>_lin, then it should know that `e` is
// always safe to use in parallel and cannot capture mutable state. Type
// system guarantee. therefore, `e` can declare its arguments as `restricted`.

#define STACK_PUSH(stack, ast_node) {stack = list_push((stack), ((value_t) { .p = (ast_node) }));}
#define STACK_POP(stack, ast_node)  {stack = list_pop((stack), (value_t*)&(ast_node));}

typedef list_t stack_s;

typedef enum AST_COMBINATOR {
  AST_C_PAR,
  AST_C_SEQUENCE,
  AST_C_JOIN,
  AST_C_REDUCE,
  AST_C_PRUNE,
  AST_C_EXTRACT,
  AST_C_EACH,
  AST_C_DISTINCT,
  AST_C_INTERSECTION,
  AST_C_GROUPBY,
  AST_C_ZIP
} AST_COMBINATOR;

/* typedef enum AST_VAL */
/* { */
/*   VAL, */
/*   FUTURE, */
/*   FUTUREPAR, */
/*   PAR, */
/*   ARRAY */
/* } AST_VAL; */

// depending on this flag, the tracing function casts the `ast_expr_t`
// in `delayed_par_t` to the appropriate AST node.
// TODO: I believe this could be internal to the struct, not internal to the file
//       (easier to reason about)
typedef enum AST_PAR_FLAG
{
  AST_EXPR_PAR, // Matches ast_expr_t* in `v`
  AST_EXPR_TWO_PAR_SRC, // Matches ast_two_par_tsource_t* in `v`
  AST_EXPR_REDUCE, // Matches ast_reduce_t* in `v`
  AST_DELAY_TREE, // Matches ast_delay_par_t* in `v`
  AST_DELAY_PAR_VALUE, // Matches a ast_delay_t* value, i.e. delay
  AST_PAR_VALUE      // Matches a par_t* that is not "delayed"
} AST_PAR_FLAG;

/*

 * enum AST_COMBINATOR tag:
   used to keep track of the mode of the combinator, e.g. whether >>_lin or >>_read

 * value_t result:
   used to store intermediate results that may be used by aliased pointers. e.g.

       val p = delay(34) >>_read e1
       val p2 = p >>_read e2

   by saving the result produced by e1, p2 does not need to recompute e1 and
   can just used its value. this works when the combinators are 'read'. if they
   were 'linear', there is no need to save any information in the `result` field.

   TODO: because the `result` value may be used between ParTs running in parallel,
   it needs to be updated atomically. At the same time, we wish not to start
   the same computation twice, so there should be a running flag(?) and/or
   a way to attach / communicate that the result is ready.

*/
// TODO: should linear be an enum mode: LINEAR, ACTOR, READ (no other mode makes sense in the ParT)
#define DEFINE_AST(NAME) \
    closure_t * expr; \
    pony_type_t * type; \
    delayed_par_t *NAME; \
    value_t result; \
    enum AST_COMBINATOR tag; \
    bool linear; \


typedef struct ast_delay_t
{
  delay_t *expr;
  pony_type_t const * type;
  bool linear;
} ast_delay_t;

typedef struct ast_expr_t
{
  DEFINE_AST(ast)
  char padding[3];
} ast_expr_t;

typedef struct ast_reduce_t
{
  DEFINE_AST(ast)
  encore_arg_t init; // TODO: this is a realised value. should it be delayed?
  pony_type_t *initType;
} ast_reduce_t;

typedef struct ast_two_par_tsource_t
{
  delayed_par_t *right;
  DEFINE_AST(left)
  char padding[3];
} ast_two_par_tsource_t;

typedef struct ast_delay_par_t
{
  delayed_par_t *left;
  delayed_par_t *right;
  pony_type_t *type;
} ast_delay_par_t;

typedef struct delayed_par_t {
    union ParT {
      /*
       * COMBINATOR AST NODES
       */

      // single AST combinators, e.g. >> or filter
      struct ast_expr_t *ast_expr;

      // reduce combinator as AST
      struct ast_reduce_t *ast_reduce;

      // combinators that take two AST sources, e.g. zip
      struct ast_two_par_tsource_t *ast_twosource;

      /*
       * VALUES AS DELAYED COMPUTATIONS
       */

      // a ParT value that has been delayed: delay(f())
      ast_delay_t *ast_par;

      ast_delay_par_t *ast_tree;

      // a realised ParT value: v_1 || v_2
      par_t *par;
    } v;

    // runtime type of the result produced by the AST node. NOT the tracing type!
    pony_type_t *type;

    // indicates how to treat the v
    AST_PAR_FLAG flag;

    bool cached;
    char padding[3]; // unused
} delayed_par_t;

// TODO: extend party_trace() to deal with delayed_parties.
pony_type_t party_delay_type =
{
  .id=ID_DELAY_PARTY,
  .size=sizeof(struct delayed_par_t),
  .trace=party_delay_trace
};

#define trace_ast(TYPE, SRC, NAME) ({ \
  TYPE *astExpr = SRC; \
  closure_trace(ctx, astExpr->expr); \
  pony_trace(ctx, &astExpr->type); \
  encore_trace_object(ctx, astExpr->NAME, party_delay_type.trace); \
  par_t *par = astExpr->result.p; \
  encore_trace_object(ctx, par, party_trace); \
  astExpr; \
}) \

// TODO: finish other cases!
void party_delay_trace(pony_ctx_t* ctx, void* p)
{
  assert(p);
  delayed_par_t *ast = (delayed_par_t*)p;
  switch(ast->flag)
  {
    case AST_EXPR_PAR: {
      trace_ast(ast_expr_t, ast->v.ast_expr, ast);
      break;
    }
    case AST_EXPR_TWO_PAR_SRC: {
      ast_two_par_tsource_t *astExpr = trace_ast(ast_two_par_tsource_t, ast->v.ast_twosource, left);
      encore_trace_object(ctx, astExpr->right, party_delay_type.trace);
      break;
    }
    case AST_EXPR_REDUCE: {
      ast_reduce_t *astExpr = trace_ast(ast_reduce_t, ast->v.ast_reduce, ast);

      // TODO: trace of the runtime type so that it is not collected?
      pony_trace(ctx, &astExpr->initType);

      // TODO: is it like this?
      encore_trace_object(ctx, astExpr->init.p, astExpr->initType->trace);
      break;
    }
    case AST_DELAY_PAR_VALUE: {
      ast_delay_t *delay = ast->v.ast_par;

      // TODO: trace of the runtime type so that it is not collected?
      pony_trace(ctx, &delay->type);

      // TODO: check if this is correct.
      encore_trace_object(ctx, delay->expr, closure_trace);
      break;
    }
    case AST_PAR_VALUE: {
      encore_trace_object(ctx, ast->v.par, party_type.trace);
      break;
    }
    case AST_DELAY_TREE: {
      party_delay_trace(ctx, ast->v.ast_tree->left);
      party_delay_trace(ctx, ast->v.ast_tree->right);
      break;
    }
  }
}

static inline pony_type_t*
ast_get_type(delayed_par_t *ast)
{
  // TODO: maintain the assert to check that the refactorings are still correct.
  switch(ast->flag)
  {
    case AST_EXPR_PAR: {
      assert(ast->type == ast->v.ast_expr->type);
      return ast->v.ast_expr->type;
    }
    case AST_EXPR_TWO_PAR_SRC: {
      assert(ast->type == ast->v.ast_twosource->type);
      return ast->v.ast_twosource->type;
    }
    case AST_EXPR_REDUCE: {
      assert(ast->type == ast->v.ast_reduce->type);
      return ast->v.ast_reduce->type;
    }
    case AST_DELAY_PAR_VALUE: {
      assert(ast->type == ast->v.ast_par->type);
      return ast->v.ast_par->type;
    }
    case AST_DELAY_TREE: {
      assert(ast->type == ast->v.ast_tree->type);
      return ast->v.ast_tree->type;
    }
    case AST_PAR_VALUE: {
      assert(ast->type == party_get_type(ast->v.par));
      return party_get_type(ast->v.par);
    }
  }
}

#define new_delay_par(FLAG, TYPE, SOURCE, ...) ({ \
   delayed_par_t *ast_node = encore_alloc(*ctx, sizeof* ast_node); \
   *ast_node = (delayed_par_t) {.flag = FLAG, \
                                .cached = false, \
                                .type = TYPE, \
                                __VA_ARGS__}; \
   switch(FLAG){ \
     case AST_EXPR_TWO_PAR_SRC: { \
       *ast_node = (delayed_par_t) {.v = {.ast_twosource = (void*) SOURCE}}; break; \
     }\
     case AST_EXPR_REDUCE: { \
       *ast_node = (delayed_par_t) {.v = {.ast_reduce = (void*) SOURCE}}; break; \
     } \
     case AST_EXPR_PAR: { \
       *ast_node = (delayed_par_t) {.v = {.ast_expr = (void*) SOURCE}}; break; \
     } \
     case AST_DELAY_TREE: { \
       *ast_node = (delayed_par_t) {.v = {.ast_tree = (void*) SOURCE}}; break; \
     } \
     case AST_DELAY_PAR_VALUE: { \
       *ast_node = (delayed_par_t) {.v = {.ast_expr = (void*) SOURCE}}; break; \
     } \
     case AST_PAR_VALUE: { \
       *ast_node = (delayed_par_t) {.v = {.par = (void*) SOURCE}}; break; \
     } \
   }\
   ast_node; \
}) \

delayed_par_t*
new_delayed_realised_par_value(pony_ctx_t **ctx, par_t * const par, pony_type_t const * const type)
{
  return new_delay_par(AST_PAR_VALUE, type, par);
}

// TODO: pass in the mode
delayed_par_t*
new_delayed_par_value(pony_ctx_t **ctx, delay_t * const val, pony_type_t const * const rtype)
{
  ast_delay_t *const delay_expr = encore_alloc(*ctx, sizeof* delay_expr);
  *delay_expr = (ast_delay_t){.expr = val,
                              .type = rtype,
                              .linear=false};
  return new_delay_par(AST_DELAY_PAR_VALUE, rtype, delay_expr);
}

delayed_par_t*
new_delayed_par_merge(pony_ctx_t **ctx, delayed_par_t *left,
                      delayed_par_t *right, pony_type_t const * const rtype)
{
  ast_delay_par_t *tree = encore_alloc(*ctx, sizeof* tree);
  *tree = (ast_delay_par_t) {.left = left,
                             .right = right,
                             .type = rtype};

  return new_delay_par(AST_DELAY_TREE, rtype, tree);
}

static inline delayed_par_t*
new_expr_ast(pony_ctx_t **ctx, delayed_par_t *ast, closure_t* const closure,
             pony_type_t const * const rtype, AST_COMBINATOR combinator)
{
  ast_expr_t *expr_node = encore_alloc(*ctx, sizeof* expr_node);
  *expr_node = (ast_expr_t) {.tag = combinator,
                             .linear = false,
                             .expr = closure,
                             .type = rtype,
                             .ast = ast};

  return new_delay_par(AST_EXPR_PAR, rtype, expr_node);
}

static inline delayed_par_t*
new_two_par_source_ast(pony_ctx_t **ctx, delayed_par_t *ast_left, delayed_par_t *ast_right,
                       closure_t *closure, pony_type_t const * const type, AST_COMBINATOR combinator)
{
  ast_two_par_tsource_t *expr_node = encore_alloc(*ctx, sizeof* expr_node);
  *expr_node = (ast_two_par_tsource_t) {.tag = combinator,
                                        .linear = false,
                                        .expr = closure,
                                        .type = type,
                                        .left = ast_left,
                                        .right = ast_right};

  return new_delay_par(AST_EXPR_TWO_PAR_SRC, type, expr_node);
}

delayed_par_t*
delay_cache_realised_part(pony_ctx_t **ctx, delayed_par_t *par)
{
  (void) ctx;
  return par;
}

delayed_par_t*
delay_cache_ast(pony_ctx_t **ctx, delayed_par_t *ast)
{
  (void) ctx;
  __atomic_test_and_set((void*)ast->cached, __ATOMIC_RELAXED);
  return ast;
}

delayed_par_t*
delay_sequence(pony_ctx_t **ctx, delayed_par_t *p, closure_t* const closure,
               pony_type_t * rtype)
{
  return new_expr_ast(ctx, p, closure, rtype, AST_C_SEQUENCE);
}

delayed_par_t*
delay_join(pony_ctx_t **ctx, delayed_par_t *p)
{
  return new_expr_ast(ctx, p, NULL, ast_get_type(p), AST_C_JOIN);
}

delayed_par_t*
delay_each(pony_ctx_t **ctx, delay_t * const val, pony_type_t const * const type)
{
  delayed_par_t *ast = new_delay_par_value(ctx, val, type);
  return new_expr_ast(ctx, ast, NULL, type, AST_C_EACH);
}

// this combinator does the analysis, decides whether to run in parallel,
// performs task fusion, etc.
// Step 1. Make it works without any analysis, just interpret the AST.
// Step 2. Use mode information to know which computations need to be realised
//         e.g. read ParT where there is aliasing of the ParT (known by the compiler).
//         e.g. linear ParT re-uses structure
// Step 3. Consider using a single ParT to prune faster
// Step 4. Based on mode information:
//         1. Fuse computations a la transducers (if there is a transducer)
//         2. Function composition
//         3. re-use of `read ParT` when its RC is 0 (has not been shared),
//            this is generated by the compiler at the end of the method when
//            if the ParT has not been shared with an actor or with another ParT


#define run_delay_par_value(ctx, AST) ({         \
  par_t *par = NULL; \
  do { \
    ast_delay_t *delay_value = AST->v.ast_par;                     \
    par =  (par_t*) closure_call(&ctx, (closure_t*) delay_value->expr, (value_t[]){}).p; \
  } while (0); \
  par; \
})

par_t*
run_delay_par(pony_ctx_t **ctx, delayed_par_t *p)
{
  switch(p->flag){
  case AST_PAR_VALUE: {
    return p->v.par;
  }
  case AST_DELAY_PAR_VALUE: {
    return run_delay_par_value(*ctx, p);
  }
  case AST_EXPR_PAR: {
    break;
  }
  case AST_EXPR_TWO_PAR_SRC: {
    break;
  }
  case AST_DELAY_TREE: {
    break;
  }
  case AST_EXPR_REDUCE: {
    break;
  }
  }
  return NULL;
}

/* static inline par_t* */
/* interpret_ast_combinator(); */

/* static inline par_t* */
/* interpret_ast_value(); */

/* static inline par_t* */
/* interpret_ast_node(pony_ctx_t **ctx, delayed_par_t *ast) */
/* { */
/*   stack_t *stack = NULL; */
/*   par_t *seed_par = NULL; */
/*   while(ast){ */
/*     switch(ast->flag){ */
/*     case AST_PAR_VALUE: { */
/*       par_t *par = interpret_ast_value(ctx, ast); */
/*       STACK_POP(stack, ast); */
/*     } */
/*     case AST_DELAY_PAR_VALUE: { */
/*       ast_delay_t *delay_value = p->v.ast_par; */
/*       return (par_t*) closure_call(ctx, (closure_t*) delay_value->expr, (value_t[]){}).p; */
/*     } */
/*     case AST_EXPR_PAR: { */
/*       break; */
/*     } */
/*     case AST_EXPR_TWO_PAR_SRC: { */
/*       break; */
/*     } */
/*     case AST_EXPR_REDUCE: { */
/*       break; */
/*     } */
/*     } */
/*   } */
/* } */

par_t*
delay_extract(pony_ctx_t **ctx, delayed_par_t *ast)
{
  while(ast){
    switch(ast->flag){
      case AST_PAR_VALUE: {
        return party_extract(ctx, ast->v.par, party_get_type(ast->v.par));
      }
      case AST_DELAY_PAR_VALUE: {
        return run_delay_par_value(*ctx, ast);
      }
      case AST_DELAY_TREE: {
        break;
      }
      case AST_EXPR_PAR: {
        /* return interpret_ast_node(ctx, ast); */
        break;
      /* ast_expr_t *expr = ast->v.ast_expr; */
      /* par_t *p2 = run_delay_par(ctx, expr->ast); */
      /* par_t *p3 = party_sequence(ctx, p2, expr->expr, expr->type); */
      /* return p3; */
      }
      case AST_EXPR_TWO_PAR_SRC: {
        break;
      }
      case AST_EXPR_REDUCE: {
        break;
      }
    }
    // TODO: update p
  }
  exit(-1);
  return NULL;
}

// TODO: `init` is a realised value. is there any advantage / use case for a
//       delayed init value, e.g. init = delay(p)?
delayed_par_t*
delay_reduce(pony_ctx_t **ctx, delayed_par_t * const ast, encore_arg_t init,
             closure_t * const closure, pony_type_t const * const resultType,
             pony_type_t const * const initType)
{
  ast_reduce_t *expr_node = encore_alloc(*ctx, sizeof* expr_node);
  *expr_node = (ast_reduce_t) {.tag = AST_C_REDUCE,
                               .linear = false,
                               .expr = closure,
                               .type = resultType,
                               .ast = ast,
                               .init = init,
                               .initType = initType };

  return new_delay_par(AST_EXPR_REDUCE, resultType, expr_node);
}

delayed_par_t*
delay_intersection(pony_ctx_t **ctx, delayed_par_t *ast_left, delayed_par_t *ast_right,
                   closure_t *cmp, pony_type_t const * const type)
{
  return new_two_par_source_ast(ctx, ast_left, ast_right, cmp, type, AST_C_INTERSECTION);
}

delayed_par_t*
delay_distinct(pony_ctx_t **ctx, delayed_par_t *ast, closure_t *cmp, pony_type_t const * const type)
{
  return new_expr_ast(ctx, ast, cmp, type, AST_C_DISTINCT);
}

delayed_par_t*
delay_zip_with(pony_ctx_t **ctx, delayed_par_t *ast_left, delayed_par_t *ast_right,
               closure_t *closure, pony_type_t const * const type)
{
  return new_two_par_source_ast(ctx, ast_left, ast_right, closure, type, AST_C_ZIP);
}

// 1. Analyse nodes: based on mode information, detect function composition
//                   possibilities, POOL_ALLOC (no need to trace structure, needs to
//                   be guided by the compiler, works for all linear ParT paths),
//                   cost-based analysis (wide combinators), prune selection.
// 2. Function fusion (function composition)
// 3. Prune selection: if there is a value or a fut and no combinator that
//      possibly returns empty Par, then run the value through the pipeline
//      and do not run anything else.

/* static void* */
/* analyse_ast(delayed_par_t *ast) */
/* { */
/*   (void) ast; */
/*   return NULL; */
/* } */
