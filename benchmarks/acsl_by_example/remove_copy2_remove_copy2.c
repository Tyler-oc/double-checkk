#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
remove_copy2(const value_type* a, size_type n, value_type* b, value_type v)
{
  size_type k = 0u;

  for (size_type i = 0u; i < n; ++i) {
    if (a[i] != v) {
      b[k++] = a[i];

    }
  }

  return k;
}