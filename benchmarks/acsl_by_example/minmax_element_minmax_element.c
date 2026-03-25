#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type_pair
minmax_element(const value_type* a, size_type n)
{
  if (0u < n) {
    size_type min = 0u;
    size_type max = 0u;

    for (size_type i = 0u; i < n; i++) {
      if (a[i] >= a[max]) {
        max = i;
      }

      if (a[i] < a[min]) {
        min = i;
      }
    }

    return make_pair(min, max);
  }

  return make_pair(n, n);
}