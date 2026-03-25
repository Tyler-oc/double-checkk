#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
stack_push_wd(Stack* s, Stack* t, value_type v)
{
  stack_push(s, v);
  stack_push(t, v);

}