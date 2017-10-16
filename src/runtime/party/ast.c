#include "ast.h"

typedef struct ASTPar_t
{
  delay_t *expr;
  pony_type_t *type;
} ASTPar_t;

/* typedef struct ExprCombinator_t ASTNode_t; */

typedef struct ExprCombinator_t
{
  DEFINE_AST
} ExprCombinator_t;

typedef struct ExprReduce_t
{
  DEFINE_AST
  encore_arg_t init;
} ExprReduce_t;

typedef struct ExprTwoParTSource_t
{
  DEFINE_AST
  union ParT2 {
    struct ExprCombinator_t *expr;
    par_t * par;
  } par_expr2;
} ExprTwoParTSource_t;

ASTPar_t*
new_delay_par(pony_ctx_t **ctx, delay_t * const val, pony_type_t const * const rtype)
{
  ASTPar_t * const exp = encore_alloc(*ctx, sizeof* exp);
  *exp = (ASTPar_t) {.type = rtype, .expr = val};
  return exp;
}

// All Expression combinators have always a source (ParT) and
// a transformation function (lambda). Based on the tag, cast
// the ExprValue_t to the appropriate combinator expression to
// access 'hidden' fields. You can think of this struct as the
// parent of any other more complex expression, i.e.
//
//                  ExprCombinator_t (>>, join, extract, each, distinct)
//                        /\
//                       /  \
//   (reduce) ExprReduce_t   ExprTwoParTSource_t (intersection, zip)
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

/* new_expr_ast(); */
/* new_reduce_ast(); */
/* new_twoSource_ast(); */

ASTPar_t*
delay_sequence(pony_ctx_t **ctx, ASTPar_t *p, closure_t* const closure,
               pony_type_t const * const rtype)
{
  ExprCombinator_t *e = newAST()
}

ASTPar_t*
  delay_join(pony_ctx_t **ctx, ASTPar_t *p)
{
}

par_t*
delay_extract(pony_ctx_t **ctx, ASTPar_t *p)
{
}

ASTPar_t*
delay_each(pony_ctx_t **ctx, delay_t * const val)
{
}

ASTPar_t*
delay_reduce(pony_ctx_t **ctx, ASTPar_t * const p, encore_arg_t init,
             closure_t * const closure, pony_type_t * type)
{
}

ASTPar_t*
delay_intersection(pony_ctx_t **ctx, ASTPar_t *par_left, ASTPar_t *par_right,
                   closure_t *cmp, pony_type_t *type)
{
}

ASTPar_t*
delay_distinct(pony_ctx_t **ctx, ASTPar_t *par, closure_t *cmp, pony_type_t *type)
{
}

ASTPar_t*
delay_zip_with(pony_ctx_t **ctx, ASTPar_t *pl, ASTPar_t *pr,
               closure_t *fn, pony_type_t *type)
{
}
