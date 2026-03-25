#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
copy_backward(const value_type* a, size_type n, value_type* b)
{
  
  for (size_type i = n; i > 0u; --i) {
    b[i - 1u] = a[i - 1u];
  }
}