#include "arrays.h"

void array_actor_trace(void* p)
{
  array_actor_t* self = (array_actor_t*)p;
  pony_trace(self->array);

  for(uint64_t i = 0; i < self->count; i++)
  {
    pony_traceactor(self->array[i]);
  }
}

void array_uint64_trace(void* p)
{
  array_uint64_t* self = (array_uint64_t*)p;
  pony_trace(self->array);
}