#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
bubble_sort(value_type* a, size_type n)
{
  if (0 < n) {
    
    for (size_type i = 1u; i < n; ++i) {
      
      for (size_type j = 0u; j < n - i; ++j) {
        if (a[j] > a[j + 1u]) {

          swap(&a[j], &a[j + 1u]);

        }
      }
    }
  }

}