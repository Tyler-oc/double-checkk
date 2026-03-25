#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
merge(const value_type* a, size_type m,
      const value_type* b, size_type n, value_type* c)
{
  
  size_type i = 0;
  size_type j = 0;
  size_type x = 0;

  if (0 < m || 0 < n) {
    
    while (i < m && j < n) {
      if (a[i] < b[j]) {
        c[x++] = a[i++];

      }
      else {
        c[x++] = b[j++];

      }

    }

    if (i < m) {

      copy(a + i, m - i, c + x);

    }
    else {

      copy(b + j, n - j, c + x);

    }

  }
}