#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
push_heap(value_type* a, size_type n)
{
  if (1u < n) { // otherwise nothings needs to be done
    size_type c = n - 1u;
    size_type p = heap_parent(c);

    if (a[p] < a[c]) {
      const value_type v  = a[c];
      a[c] = a[p];

      for (c = p, p = heap_parent(c); 0u < c && a[p] < v;
           c = p, p = heap_parent(c)) {
        
        if (a[c] < a[p]) {
          a[c] = a[p];

        }
      }

      a[c] = v;

    }
  }
}