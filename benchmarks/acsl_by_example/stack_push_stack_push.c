#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
stack_push(Stack* s, value_type v)
{
  if (!stack_full(s)) {
    
    s->obj[s->size++] = v;
  }
}