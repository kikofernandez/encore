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
