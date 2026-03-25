#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
partial_sort(value_type* a, size_type m, size_type n)
{
  if (m > 0u) {
    make_heap(a, m);

    for (size_type i = m; i < n; ++i) {
      if (a[i] < a[0u]) {
        
        pop_heap(a, m);

        swap(a + m - 1u, a + i);

        push_heap(a, m);

      }
    }

    sort_heap(a, m);

  }
}