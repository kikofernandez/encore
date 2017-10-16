#include "ast.h"

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
