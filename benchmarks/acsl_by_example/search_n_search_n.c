#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
search_n(const value_type* a, size_type n, value_type v, size_type p)
{
  if (0u < p) {
    if (p <= n) {
      size_type start = 0u;

      for (size_type i = 0u; i < n; ++i) {
        if (a[i] != v) {
          start = i + 1u;
          
        }
        else {

          if (p == i + 1u - start) {

            return start;
          }
          else {
            
            continue;
          }
        }

      }

      return n;
    }
    else {

      return n;
    }
  }
  else {

    return 0u;
  }
}