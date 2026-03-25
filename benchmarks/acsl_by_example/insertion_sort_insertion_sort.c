#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
insertion_sort(value_type* a, size_type n)
{
  
  for (size_type i = 0u; i < n; ++i) {
    const size_type k = upper_bound(a, i, a[i]);

    rotate(a + k, i - k, i + 1u - k);

  }

}