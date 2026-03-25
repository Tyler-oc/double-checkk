#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
pop_heap(value_type* a, size_type n)
{
  if (1u < n) {
    
    if (a[n - 1u] < a[0u]) { // otherwise a[0] == a[n-1] and nothing to be done
      size_type p = 0u;
      const value_type v = a[n - 1u];
      a[n - 1u] = a[p];

      size_type c = heap_child(a, n - 1u, p);

      for (; c < n - 1u && v < a[c];  p = c, c = heap_child(a, n - 1u, p)) {

        if (a[c] < a[p]) {
          a[p] = a[c];

        }
      }

      a[p] = v;

    }
  }
}