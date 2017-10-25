#ifndef INTERPRETER_H_20171025
#define INTERPRETER_H_20171025

/*
 * This header declares common interpreters for delayed ParTs.
 */

#include "party.h"

/** Interpret the delayed ParT realising unfinished values.
 *
 * Interprets the ParT realising values, blocking if necessary.
 * This operation returns a new ParT were all items have been realised.
 *
 * @param ctx Context
 * @param p A ParT with possibly ongoing computations
 * @param type The runtime type of the ParT
 * @return ParT
 */

#define interpreter_to_blocking_delayed_party(ctx, PARTY, type) _Generic((PARTY)), \
    par_t * : interpreter_to_realised_party, \
    delayed_par_t * : interpreter_to_realised_delayed_party, \
    default: interpreter_to_realised_delayed_party \
    )(ctx, PARTY, type)

delayed_par_t*
interpreter_to_realised_party(pony_ctx_t **ctx, par_t * p, pony_type_t *type);

delayed_par_t*
interpreter_to_realised_delayed_party(pony_ctx_t **ctx, delayed_par_t * p, pony_type_t *type);

#endif
