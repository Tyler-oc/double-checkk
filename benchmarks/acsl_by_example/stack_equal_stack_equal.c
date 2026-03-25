#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

bool
stack_equal(const Stack* s, const Stack* t)
{
  return (s->size == t->size) && equal(s->obj, s->size, t->obj);
}