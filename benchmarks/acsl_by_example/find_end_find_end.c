#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
find_end(const value_type* a, size_type n,
         const value_type* b, size_type p)
{
  size_type r = n;

  if ((0u < p) && (p <= n)) {
    
    for (size_type i = 0u; i <= n - p; ++i) {
      if (equal(a + i, p, b)) {
        r = i;
      }
    }
  }

  return r;
}