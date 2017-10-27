#include "party.h"
#include <assert.h>
#include "list.h"
#include "interpreter.h"

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

// NOTE: I believe this could be internal to the struct, not internal to the file
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

   this also implies that a result has type `par_t *`, i.e. we forbid having
   `delayed_par_t*`. this needs to be known because we need to know which
   operations we can use on the result: part_sequence, etc or delayed_sequence?

   this design decision forbids results that contain intermediate results,
   some parTs could be `par_t*` and some others `delayed_par_t*`.

*/

// NOTE: should linear be an enum mode: LINEAR, ACTOR, READ (only these modes make sense in the ParT)
#define DEFINE_AST(NAME) \
    delay_t * expr; \
    pony_type_t * type; \
    delayed_par_t *NAME; \
    value_t result; \
    enum AST_COMBINATOR tag; \
    bool linear; \

typedef struct ast_delay_t
{
  delay_t *expr;
  void *result;
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

      // a delay ParT merged: (delayed_par_t AST1) || (delayed_par_t AST2)
      ast_delay_par_t *ast_tree;

      // a realised ParT value: v_1 || v_2
      par_t *par;
    } v;

    // runtime type of the result produced by the AST node. NOT the tracing type!
    pony_type_t *type;

    // indicates how to treat the union, a.k.a. `v`
    AST_PAR_FLAG flag;

    // a cached delay ParT keeps the intermediate result, e.g. does not
    // perform an optimisation. e.g.
    //
    //    val p2 = cache(p >> e1)
    //    val p3 = p2 >> e2
    //    val p4 = p2 >> e3
    //
    // the result of p2 will be saved. if not, p2 >> e2 and p2 >> e3
    // run the same initial computation twice, p >> e1. this is similar
    // to Spark RDDs and Sparks in Haskell.
    //
    bool cached;
    bool running;
    char padding[10]; // unused
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
  encore_trace_object(ctx, astExpr->NAME, party_delay_type.trace); \
  par_t *par = astExpr->result.p; \
  encore_trace_object(ctx, par, party_trace); \
  astExpr; \
}) \

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

      // NOTE: check if this is correct
      encore_trace_object(ctx, astExpr->init.p, astExpr->initType->trace);
      break;
    }
    case AST_DELAY_PAR_VALUE: {
      ast_delay_t *delay = ast->v.ast_par;

      // NOTE: check if this is correct.
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
  // NOTE: maintain the assert to check that the refactorings are still correct.
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
                                .running = false, \
                                .cached = false, \
                                .type = TYPE, \
                                .v = { (void*) SOURCE },        \
                                __VA_ARGS__}; \
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
                             .expr = (delay_t *) closure,
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
                                        .expr = (delay_t *) closure,
                                        .type = type,
                                        .left = ast_left,
                                        .right = ast_right};
  return new_delay_par(AST_EXPR_TWO_PAR_SRC, type, expr_node);
}

delayed_par_t*
delay_cache_realised_part(pony_ctx_t **ctx, delayed_par_t *par)
{
  // The ParT is already a value, nothing to do.
  (void) ctx;
  return par;
}

delayed_par_t*
delay_cache_ast(pony_ctx_t **ctx, delayed_par_t *ast)
{
  (void) ctx;
  __atomic_test_and_set(&ast->cached, __ATOMIC_RELAXED);
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



/** interpret expression where the input values have already been realised
 *
 * Interprets an expression (which we know can only be >>, join, each or distinct),
 * given as input a realised ParT. Basically, this interpreter glues together
 * delayed ParTs as AST nodes with realised ParTs that are possibly running.
 *
 * precondition: values[0] must be a realised ParT
 * precondition: values[1] must be a delayed_par_t that contains the expresion (closure)
 *               to run on the items of the ParT
 *
 * @param ctx Context.
 * @param values Array where values[0] is a `par_t*` type and values[1] is a
 *               `delayed_par_t*` that contains the expression to apply to the ParT.
 * @param type Runtime type.
 * @return Delayed ParT that contains ongoing computations, i.e. wrapper around a ParT.
 */
static inline delayed_par_t*
interpreter_to_realised_ast_expr_par(pony_ctx_t **ctx, void ** values, pony_type_t *type)
{
  (void) type;
  void *result = values[0];
  delayed_par_t *ast = values[1];
  ast_expr_t *ast_expr = ast->v.ast_expr;
  AST_COMBINATOR tag = ast_expr->tag;
  delay_t *e = ast_expr->expr;
  pony_type_t *rtype = ast_expr->type;

  switch(tag){
    case AST_C_SEQUENCE: {
      par_t *ps = party_sequence(ctx, result, (void*) e, rtype);
      return new_delay_par_value(ctx, ps, party_get_type(ps));
    }
    case AST_C_JOIN: {
      par_t *pj = party_join(ctx, result);
      return new_delay_par_value(ctx, pj, party_get_type(pj));
    }
    case AST_C_EACH: {
      // result is: each([t]) : Par[t]. this is already a realised ParT.
      return new_delay_par_value(ctx, (par_t *) result, party_get_type(result));
    }
    case AST_C_DISTINCT: {
      par_t *pd = party_distinct(ctx, result, (void *) e, rtype);
      return new_delay_par_value(ctx, pd, party_get_type(pd));
    }
    default: {
      exit(-1);
    }
  }
  exit(-1);
}


/** interpret an AST node where the input values have not been realised yet
 *
 * Interprets an AST node, recursively, until it cannot be reduced, i.e. realised
 * anymore. A realised node is one that has the form of a `par_t*`.
 *
 * @param ctx Context.
 * @param ast a `delayed_par_t*` that contains the expression to, possibly, realised
.*            e.g. delay(34) >> e1, unevaluated.
 * @param type Runtime type.
 * @return Delayed ParT that contains ongoing computations, i.e. wrapper around a ParT.
 */
delayed_par_t*
interpreter_to_realised_delayed_party(pony_ctx_t **ctx, delayed_par_t * ast, pony_type_t *type)
{
  // TODO: this function blocks if it encounters a value that's not realised.
  // At this point, we could imagine spawning more tasks to get the delayed
  // computations going, i.e. delay(f()), because it is a closure.
  stack_s *stack = NULL;
  par_t *seed_par = new_par_empty(ctx, type);

  while(ast){
    switch(ast->flag){
      case AST_PAR_VALUE: {
        seed_par = new_par_p(ctx, seed_par, ast->v.par, &party_type);
        STACK_POP(stack, ast);
        break;
      }
      case AST_DELAY_PAR_VALUE: {
        // TODO: it seems almost like a copy-paste from AST_EXPR_PAR
        bool cached = __atomic_load_n(&ast->cached, __ATOMIC_ACQUIRE);

        ast_delay_t *delay_value = ast->v.ast_par;

        if (cached) {
          bool running = __atomic_exchange_n(&ast->running, true, __ATOMIC_ACQ_REL);

          if (!running) {

            // Then we run the computation and save
            void *par = closure_call(ctx, (closure_t*) delay_value->expr, (value_t[]){}).p;
            __atomic_store(&delay_value->result, &par, __ATOMIC_RELEASE);
            seed_par = new_par_p(ctx, seed_par, par, &party_type);

          } else {

            // we wait for the result or the result is already there
            // NOTE: isn't result.p already `void*`. the compiler doesn't let me.
            par_t *result = __atomic_load_n(&delay_value->result, __ATOMIC_ACQUIRE);

            if (!result) {

              // result has not been set yet.

              // Either attach computation to be run by the other thread or block.
              // This is difficult because by the time I attach the computation,
              // the other thread may already have exit.

              // TODO:
              (void)NULL;
              exit(-1);

            } else {
              // there is a result
              seed_par = new_par_p(ctx, seed_par, result, &party_type);
            }
          }
        } else {
          par_t *p = (par_t*) closure_call(ctx, (closure_t*) delay_value->expr, (value_t[]){}).p;
          seed_par = new_par_p(ctx, seed_par, p, &party_type);
        }

        STACK_POP(stack, ast);
        break;
      }
      case AST_DELAY_TREE: {
        ast_delay_par_t *delay_par = ast->v.ast_tree;
        STACK_PUSH(stack, delay_par->right);
        ast = delay_par->left;
        break;
      }
      case AST_EXPR_PAR: {
        // TODO: quite similar to AST_DELAY_PAR_VALUE
        bool cached = __atomic_load_n(&ast->cached, __ATOMIC_ACQUIRE);
        ast_expr_t *ast_expr = ast->v.ast_expr;

        if (cached) {
          bool running = __atomic_exchange_n(&ast->running, true, __ATOMIC_ACQ_REL);

          if (!running) {

            // Then we run the computation and save
            par_t *p = (par_t*) closure_call(ctx, (closure_t*) ast_expr->expr, (value_t[]){}).p;
            void *result = ast_expr->result.p;
            __atomic_store(&result, (void**)&p, __ATOMIC_RELEASE);
            seed_par = new_par_p(ctx, seed_par, p, &party_type);

          } else {

            // we wait for the result or the result is already there
            // NOTE: isn't result.p already `void*`. the compiler doesn't let me.
            void *result = __atomic_load_n(&ast_expr->result.p, __ATOMIC_ACQUIRE);

            if (!result) {

              // result has not been set yet.

              // Either attach computation to be run by the other thread or block.
              // This is difficult because by the time I attach the computation,
              // the other thread may already have exit.

              // TODO:
              (void)NULL;
              exit(-1);

            } else {
              // there is a result
              delayed_par_t *party =  interpreter_to_realised_ast_expr_par(ctx, (void*[]){result, ast}, type);
              seed_par = new_par_p(ctx, seed_par, party->v.par, &party_type);
            }
          }
        } else {
          // not cached, run all computations
          // e.g. (delay f() || delay(f())) >> foo
          // start by interpreting the inner AST, a.k.a. (delay f() || delay(f()))
          // return a ParT (it may be fully realised or with ongoing computations)
          delayed_par_t *dp = interpreter_to_realised_delayed_party(ctx, ast_expr->ast, ast_expr->type);

          // take ParT and apply pending computations, ParT >> foo
          delayed_par_t *party = interpreter_to_realised_ast_expr_par(ctx, (void*[]){dp->v.par, ast}, type);

          // add result to ongoing seed / result value
          seed_par = new_par_p(ctx, seed_par, party->v.par, &party_type);
        }
        STACK_POP(stack, ast);
        break;
      }
      case AST_EXPR_TWO_PAR_SRC: {
        exit(-1);
        break;
      }
      case AST_EXPR_REDUCE: {
        exit(-1);
        break;
      }
    }
  }

  array_t *ar = party_extract(ctx, seed_par, party_get_type(seed_par));
  par_t *parResult = new_par_array(ctx, ar, array_get_type(ar));
  return new_delay_par_value(ctx, parResult, party_get_type(parResult));
}

array_t*
delay_extract(pony_ctx_t **ctx, delayed_par_t *ast, pony_type_t *type)
{
  par_t *seed_par = new_par_empty(ctx, type);
  delayed_par_t *p = interpreter_to_realised_delayed_party(ctx, ast, type);
  return party_extract(ctx,  p->v.par, party_get_type(seed_par));
}

// NOTE: `init` is a realised value. is there any advantage / use case for a
//       delayed init value, e.g. init = delay(p)?
delayed_par_t*
delay_reduce(pony_ctx_t **ctx, delayed_par_t * const ast, encore_arg_t init,
             closure_t * const closure, pony_type_t const * const resultType,
             pony_type_t const * const initType)
{
  ast_reduce_t *expr_node = encore_alloc(*ctx, sizeof* expr_node);
  *expr_node = (ast_reduce_t) {.tag = AST_C_REDUCE,
                               .linear = false,
                               .expr = (delay_t *) closure,
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
