#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
shuffle(value_type* a, size_type n, unsigned short* seed)
{
  if (0u < n) {
    
    for (size_type i = 1u; i < n; ++i) {
      size_type k = random_number(seed, i) + 1u;

      if (k < i) {
        swap(&a[k], &a[i]);

      }
      else {

      }

    }
  }
}