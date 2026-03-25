#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

value_type
stack_top(const Stack* s)
{
  if (!stack_empty(s)) {
    return s->obj[s->size - 1u];
  }
  else {
    return s->obj[0u];
  }
}