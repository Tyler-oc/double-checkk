#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
rotate_copy(const value_type* a, size_type p, size_type n, value_type* b)
{
  copy(a,  p, b + (n - p));
  copy(a + p, n - p, b);
}