#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
stack_pop_wd(Stack* s, Stack* t)
{
  stack_pop(s);
  stack_pop(t);
}