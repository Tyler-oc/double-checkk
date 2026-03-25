#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
stack_init(Stack* s, value_type* storage, size_type capacity)
{
  s->obj      = storage;
  s->capacity = capacity;
  s->size     = 0u;
}