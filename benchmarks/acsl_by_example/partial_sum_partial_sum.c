#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
partial_sum(const value_type* a, size_type n, value_type* b)
{
  if (0u < n) {
    
    b[0u] = a[0u];

    for (size_type i = 1u; i < n; ++i) {
      b[i] = b[i - 1u] + a[i];

    }
  }

  return n;
}