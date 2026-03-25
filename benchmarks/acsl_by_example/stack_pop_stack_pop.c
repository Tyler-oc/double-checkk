#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
stack_pop(Stack* s)
{
  if (!stack_empty(s)) {
    --s->size;
  }
}