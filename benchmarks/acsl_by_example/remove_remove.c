#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
remove(value_type* a, size_type n, value_type v)
{
  size_type k = 0u;

  for (size_type i = 0u; i < n; ++i ) {
    if (a[i] != v) {
      a[k++] = a[i];

    }
  }

  return k;
}