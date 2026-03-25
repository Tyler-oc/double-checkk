#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

bool
stack_top_wd(const Stack* s, const Stack* t)
{
  return stack_top(s) == stack_top(t);
}