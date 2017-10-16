#include "party.h"

typedef enum AST_COMBINATOR {
  SEQUENCE,
  JOIN,
  REDUCE,
  PRUNE,
  EXTRACT,
  EACH,
  DISTINCT,
  INTERSECTION,
  GROUPBY
} AST_COMBINATOR;

typedef enum AST_VAL
{
  VAL,
  FUTURE,
  FUTUREPAR,
  PAR,
  ARRAY
} AST_VAL;

typedef enum AST_PAR_FLAG
{
  AST_EXPR_PAR, // Matches ExprCombinator_t* in `par_expr`
  AST_LAZY_PAR, // Matches a ASTPar_t* value, i.e. delay
  AST_PAR      // Matches a par_t* that is not "delayed"
} AST_PAR_FLAG;

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

// used in: >>, join, extract, each, distinct
#define DEFINE_AST \
    enum AST_COMBINATOR tag; \
    \
    // used to keep track of the mode of the combinator
    // e.g. whether >>_lin or >>_read
    bool linear; \
    \
    closure_t const * const expr; \
    pony_type_t const * const type; \
    \
    \
    // indicates how to treat the par_expr
    AST_PAR_FLAG flag; \
    // captures the possibility of:
    // 1. chaining a combinator to an unevaluated ParTs
    // 2. chaining a combinator to an evaluated ParT
    union ParT { \
      // another combinator AST node
      struct ExprCombinator_t *expr; \
      // a ParT value that has been delayed
      ASTPar_t *ast_par; \
      // a realised ParT value
      par_t * par; \
    } par_expr; \
