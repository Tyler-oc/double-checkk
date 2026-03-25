#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
find_first_of (const value_type* a, size_type m,
               const value_type* b, size_type n)
{
  
  for (size_type i = 0u; i < m; i++) {
    if (find2(b, n, a[i]) < n) {
      return i;
    }
  }

  return m;
}