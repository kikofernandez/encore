#ifndef PARTY_H_412139
#define PARTY_H_412139

#include "encore.h"
#include <array.h>

extern pony_type_t party_type;
extern pony_type_t party_delay_type;

typedef struct par_t par_t;
typedef struct closure_t delay_t;
typedef struct ast_delay_t ast_delay_t;
typedef struct delayed_par_t delayed_par_t;

void party_trace(pony_ctx_t*, void*);
void party_delay_trace(pony_ctx_t*, void*);
pony_type_t* party_get_type(par_t * const p);


/**
 *  Constructor of ParT types
 */
par_t* new_par_empty(pony_ctx_t **ctx, pony_type_t const * const rtype);
par_t* new_par_v(pony_ctx_t **ctx, encore_arg_t val, pony_type_t const * const rtype);
par_t* new_par_f(pony_ctx_t **ctx,future_t* const fut, pony_type_t const * const rtype);
par_t* new_par_p(pony_ctx_t **ctx, par_t* const p1, par_t* const p2, pony_type_t const * const rtype);
par_t* new_par_fp(pony_ctx_t **ctx, future_t* const f, pony_type_t const * const rtype);
par_t* new_par_array(pony_ctx_t **ctx, array_t* arr, pony_type_t const * const rtype);

/**
 *  sequence :: Par t -> (t -> t') -> Par t'
 *
 *  Given a Par t and a function, execute the function for every Par t element
 *
 *  @param p Parallel collection
 *  @param closure The closure to be called
 *  @return The pointer to the parallel collection
 */

par_t* party_sequence(pony_ctx_t **ctx, par_t* p, closure_t* const closure,
                      pony_type_t const * const rtype);

/**
 * join :: Par (Par t) -> Par t
 * @param p Parallel collection with type Par (Par t)
 * @return Pointer to a new parallel collection of type Par t
 */

par_t* party_join(pony_ctx_t **ctx, par_t* const p);

/**
 * extract :: Par t -> [t]
 *
 * Given a Par t, return an array of the computed elements in the collection
 *
 * @param p Parallel collection
 * @param type Runtime type
 * @return Pointer to an array
 */

array_t* party_extract(pony_ctx_t **ctx, par_t* p, pony_type_t *type);

/**
 * each :: [t] -> Par t
 *
 * Given an array of type t, return a Par t
 *
 * @param array Array to convert to a parallel collection
 * @return Parallel collection
 */
par_t* party_each(pony_ctx_t **ctx, array_t * const array);


/** Reduces a ParT sequentially (not in parallel).
 *
 * This function is called when we have no guarantees of the associativity
 * of the closure to run. For instance, the following reduce function
 *
 *    reduce :: Par t -> a -> (t -> a -> a) -> Par a
 *
 * can only be run in sequential order, since we do not have an associative
 * function between `a` types that can merge `a -> a -> a`. If the types `a`
 * and `t` were the same and the closure satisfies associativity, then we could
 * run this function in parallel.
 *
 * Given a Par t, an initial value and a reduce transformation function,
 * run the reduce function sequentially over the items in the ParT
 *
 * @param p Par T
 * @param init Initial argument
 * @param closure Transformation reduction function
 * @return Parallel collection
 *
 */
future_t* party_reduce_sequential(pony_ctx_t **ctx,
                                  par_t * const p,
                                  encore_arg_t init,
                                  closure_t * const closure,
                                  pony_type_t * type);


/** Reduces a ParT possibly in parallel.
 *
 * This function is used when we have a guarantee that the closure is associative:
 *
 *   reduce :: Par t -> t -> (t -> t -> t) -> Par t
 *
 * Given a Par t, an initial value and a reduce transformation function,
 * run the reduce function over the items in the ParT.
 *
 * @param p Par T
 * @param init Initial argument
 * @param closure Transformation reduction function
 * @return Parallel collection
 *
 */
future_t* party_reduce_assoc(pony_ctx_t **ctx,
                             par_t * const p,
                             encore_arg_t init,
                             closure_t * const closure,
                             pony_type_t * type);

/** Performs the intersection of ParT, possibly in parallel.
 *
 *   intersection :: Par t -> Par t -> Par t
 *
 * Given two Par t, return a new ParT with intersected elements
 *
 * @param par_left Par T
 * @param par_right Par T
 * @param cmp Comparator function to determine equality
 * @return Parallel collection
 *
 */
par_t* party_intersection(pony_ctx_t **ctx,
                          par_t *par_left,
                          par_t *par_right,
                          closure_t *cmp,
                          pony_type_t *type);

/** Return distinct elements from the ParT (removes duplicates)
 *
 *   distinct :: Par t -> Par t
 *
 * Given a Par t, return a new ParT without duplicates (distinct elements)
 *
 * @param par Par T
 * @param cmp Comparator function to determine equality
 * @return Parallel collection
 *
 */
par_t* party_distinct(pony_ctx_t **ctx,
                      par_t *par,
                      closure_t *cmp,
                      pony_type_t *type);

/** Zip two ParTs
 *
 *   zip :: Par t -> Par t' -> (t -> t' ->  t'') -> Par t''
 *
 * Given two ParT, zip them with the provided function
 *
 * @param pl Par T
 * @param pr Par T
 * @param fn Function to zip elements together
 * @return Parallel collection
 *
 */
par_t* party_zip_with(pony_ctx_t **ctx,
                      par_t *pl,
                      par_t *pr,
                      closure_t *fn,
                      pony_type_t *type);


par_t*
run_delay_par(pony_ctx_t **ctx, delayed_par_t *p);

// Creates a delayed ParT whose value can be delayed or realised, based on type information
#define new_delay_par_value(ctx, VAL, runtime_type)  _Generic((VAL), \
           par_t * : new_delayed_realised_par_value, \
           delay_t * : new_delayed_par_value, \
           default: new_delayed_par_value \
          )(ctx, VAL, runtime_type)


delayed_par_t*
new_delayed_par_value(pony_ctx_t **ctx, delay_t * const val, pony_type_t const * const rtype);

delayed_par_t*
new_delayed_realised_par_value(pony_ctx_t **ctx, par_t * const par, pony_type_t const * const type);

delayed_par_t*
new_delayed_par_merge(pony_ctx_t **ctx, delayed_par_t *d1, delayed_par_t *d2, pony_type_t const * const rtype);

// DELAY PART: combinators that extend the AST nodes given as input

#define delay_cache(ctx, VAL)  _Generic((VAL),  \
           par_t * : delay_cache_realised_part, \
           delay_t * : delay_cache_ast,         \
           default: delay_cache_ast             \
          )(ctx, VAL, runtime_type)

delayed_par_t*
delay_cache_realised_part(pony_ctx_t **ctx, delayed_par_t *ast);

delayed_par_t*
delay_cache_ast(pony_ctx_t **ctx, delayed_par_t *ast);

delayed_par_t*
delay_sequence(pony_ctx_t **ctx, delayed_par_t *ast, closure_t* const closure, pony_type_t const * const rtype);

delayed_par_t*
delay_join(pony_ctx_t **ctx, delayed_par_t *ast);

delayed_par_t*
delay_each(pony_ctx_t **ctx, delay_t * const val, pony_type_t const * const type);

par_t*
delay_extract(pony_ctx_t **ctx, delayed_par_t *p);

delayed_par_t*
delay_reduce(pony_ctx_t **ctx, delayed_par_t * const ast, encore_arg_t init,
             closure_t * const closure, pony_type_t * resultType,
             pony_type_t * initType);

delayed_par_t*
delay_intersection(pony_ctx_t **ctx, delayed_par_t *par_left, delayed_par_t *par_right,
                   closure_t *cmp, pony_type_t *type);

delayed_par_t*
delay_distinct(pony_ctx_t **ctx, delayed_par_t *par, closure_t *cmp, pony_type_t *type);

delayed_par_t*
delay_zip_with(pony_ctx_t **ctx, delayed_par_t *pl, delayed_par_t *pr,
               closure_t *fn, pony_type_t *type);
#endif
