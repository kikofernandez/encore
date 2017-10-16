#include "party.h"

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

// used in: >>, join, extract, each, distinct


typedef enum AST_COMBINATOR {
  SEQUENCE,
  JOIN,
  REDUCE,
  PRUNE,
  EXTRACT,
  EACH,
  DISTINCT,
  INTERSECTION,
  GROUPBY,
  ZIP
} AST_COMBINATOR;

typedef enum AST_VAL
{
  VAL,
  FUTURE,
  FUTUREPAR,
  PAR,
  ARRAY
} AST_VAL;

// depending on this flag, the tracing function casts the `ast_expr_t`
// in `ast_node_t` to the appropriate AST node.
typedef enum AST_PAR_FLAG
{
  AST_EXPR_PAR, // Matches ast_expr_t* in `par_expr`
  AST_EXPR_TWO_PAR_SRC, // Matches ast_two_par_tsource_t* in `par_expr`
  AST_EXPR_REDUCE, // Matches ast_reduce_t* in `par_expr`
  AST_DELAY_PAR, // Matches a ast_delay_t* value, i.e. delay
  AST_PAR      // Matches a par_t* that is not "delayed"
} AST_PAR_FLAG;

typedef struct ast_node_t {
    // indicates how to treat the par_expr
    AST_PAR_FLAG flag;
    union ParT {
      // another combinator AST node
      struct ast_expr_t *ast_expr;
      // a ParT value that has been delayed
      ast_delay_t *ast_par;
      // a realised ParT value
      par_t *par;
    } par_expr;
} ast_node_t;

/*
  used to keep track of the mode of the combinator, e.g. whether >>_lin or >>_read

  enum AST_COMBINATOR tag; \
*/
#define DEFINE_AST \
    enum AST_COMBINATOR tag; \
    bool linear; \
    closure_t const * const expr; \
    pony_type_t const * const type; \
    ast_node_t *ast; \

struct ast_delay_t
{
  delay_t *expr;
  pony_type_t *type;
};

typedef struct ast_expr_t
{
  DEFINE_AST
} ast_expr_t;

typedef struct ast_reduce_t
{
  DEFINE_AST
  encore_arg_t init; // TODO: this is a realised value. should it be delayed?
} ast_reduce_t;

typedef struct ast_two_par_tsource_t
{
  DEFINE_AST
  ast_node_t *ast_par;
} ast_two_par_tsource_t;

inline pony_type_t* ast_get_type(ast_node_t *ast)
{
  switch(ast->flag)
  {
  case AST_EXPR_PAR: {
    // Matches ast_expr_t* in `par_expr`
    return ast->par_expr.ast_expr->type;
  }
  case AST_EXPR_TWO_PAR_SRC: {
    // Matches ast_expr_t* in `par_expr`
    return ast->par_expr.ast_expr->type;
  }
  case AST_EXPR_REDUCE: {
    // Matches ast_expr_t* in `par_expr`
    return ast->par_expr.ast_expr->type;
  }
  case AST_DELAY_PAR: {
    // Matches a ast_delay_t* value, i.e. delay
    return ast->par_expr.ast_par->type;
  }
  case AST_PAR: {
    // Matches a par_t* that is not "delayed"
    return party_get_type(ast->par_expr.par);
  }
  }
}


ast_node_t*
new_delayed_realised_par(pony_ctx_t **ctx, par_t * const par, pony_type_t const * const type)
{
  (void) type;
  ast_node_t * const exp = encore_alloc(*ctx, sizeof* exp);
  *exp = (ast_node_t) {.flag = AST_PAR,
                       .par_expr = {.par = par }};
  return exp;
}

ast_node_t*
new_delayed_par(pony_ctx_t **ctx, delay_t * const val, pony_type_t const * const rtype)
{
  ast_delay_t * const delay_expr = encore_alloc(*ctx, sizeof* delay_expr);
  *delay_expr = (ast_delay_t) {.type = rtype, .expr = val};

  ast_node_t * const exp = encore_alloc(*ctx, sizeof* exp);
  *exp = (ast_node_t) {.flag = AST_DELAY_PAR,
                       .par_expr = {.ast_par = delay_expr }};
  return exp;
}

inline ast_node_t*
new_expr_ast(pony_ctx_t **ctx, ast_node_t *ast, closure_t* const closure,
             pony_type_t const * const rtype, AST_COMBINATOR combinator)
{
  ast_expr_t *expr_node = encore_alloc(*ctx, sizeof* expr_node);
  *expr_node = (ast_expr_t) {.tag = combinator,
                             .linear = false,
                             .expr = closure,
                             .type = rtype,
                             .ast = ast};

  ast_node_t *ast_node = encore_alloc(*ctx, sizeof* ast_node);
  *ast_node = (ast_node_t) {.flag = AST_EXPR_PAR,
                            .par_expr = {.ast_expr = expr_node}};
  return ast_node;
}

// TODO: `init` is a realised value. is there any advantage / use case for a
//       delayed init value, e.g. init = delay(p)?
inline ast_node_t*
new_reduce_ast(pony_ctx_t **ctx, ast_node_t *ast, closure_t* const closure,
               encore_arg_t init, pony_type_t const * const rtype, AST_COMBINATOR combinator)
{
  ast_reduce_t *expr_node = encore_alloc(*ctx, sizeof* expr_node);
  *expr_node = (ast_reduce_t) {.tag = combinator,
                               .linear = false,
                               .expr = closure,
                               .type = rtype,
                               .ast = ast,
                               .init = init };

  ast_node_t *ast_node = encore_alloc(*ctx, sizeof* ast_node);
  *ast_node = (ast_node_t) {.flag = AST_EXPR_REDUCE,
                            .par_expr = {.ast_expr = (ast_expr_t*) expr_node}};
  return ast_node;
}

inline ast_node_t*
new_two_par_source_ast(pony_ctx_t **ctx, ast_node_t *ast_left, ast_node_t *ast_right,
                       closure_t *closure, pony_type_t *type, AST_COMBINATOR combinator)
{
  ast_two_par_tsource_t *expr_node = encore_alloc(*ctx, sizeof* expr_node);
  *expr_node = (ast_two_par_tsource_t) {.tag = combinator,
                                        .linear = false,
                                        .expr = closure,
                                        .type = type,
                                        .ast = ast_left,
                                        .ast_par = ast_right};
  ast_node_t *ast_node = encore_alloc(*ctx, sizeof* ast_node);
  *ast_node = (ast_node_t) {.flag = AST_EXPR_TWO_PAR_SRC,
                            .par_expr = {.ast_expr = (ast_expr_t*) expr_node}};
  return ast_node;
}

ast_node_t*
delay_sequence(pony_ctx_t **ctx, ast_node_t *p, closure_t* const closure,
               pony_type_t const * const rtype)
{
  return new_expr_ast(ctx, p, closure, rtype, SEQUENCE);
}

ast_node_t*
delay_join(pony_ctx_t **ctx, ast_node_t *p)
{
  return new_expr_ast(ctx, p, NULL, ast_get_type(p), JOIN);
}

ast_node_t*
delay_each(pony_ctx_t **ctx, delay_t * const val, pony_type_t const * const type)
{
  ast_node_t *ast = new_delay_par(ctx, val, type);
  return new_expr_ast(ctx, ast, NULL, type, JOIN);
}

// this combinator does the analysis, decides whether to run in parallel,
// performs task fusion, etc.
// Step 1. Make it work without any analysis, just interpret the AST.
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

/* par_t* */
/* delay_extract(pony_ctx_t **ctx, ast_node_t *p) */
/* { */
/*   return NULL; */
/* } */

ast_node_t*
delay_reduce(pony_ctx_t **ctx, ast_node_t * const ast, encore_arg_t init,
             closure_t * const closure, pony_type_t * type)
{
  return new_reduce_ast(ctx, ast, closure, init, type, REDUCE);
}

ast_node_t*
delay_intersection(pony_ctx_t **ctx, ast_node_t *ast_left, ast_node_t *ast_right,
                   closure_t *cmp, pony_type_t *type)
{
  return new_two_par_source_ast(ctx, ast_left, ast_right, cmp, type, INTERSECTION);
}

ast_node_t*
delay_distinct(pony_ctx_t **ctx, ast_node_t *ast, closure_t *cmp, pony_type_t *type)
{
  return new_expr_ast(ctx, ast, cmp, type, DISTINCT);
}

ast_node_t*
delay_zip_with(pony_ctx_t **ctx, ast_node_t *ast_left, ast_node_t *ast_right,
               closure_t *closure, pony_type_t *type)
{
  return new_two_par_source_ast(ctx, ast_left, ast_right, closure, type, ZIP);
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
/* analyse_ast(ast_node_t *ast) */
/* { */
/*   (void) ast; */
/*   return NULL; */
/* } */
