#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

bool
stack_size_wd(const Stack* s, const Stack* t)
{
  return stack_size(s) == stack_size(t);
}