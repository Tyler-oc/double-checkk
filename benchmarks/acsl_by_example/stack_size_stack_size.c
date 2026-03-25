#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
stack_size(const Stack* s)
{
  return s->size;
}