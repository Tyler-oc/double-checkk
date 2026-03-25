#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

bool
stack_full(const Stack* s)
{
  return stack_size(s) == s->capacity;
}