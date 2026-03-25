#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
swap_ranges(value_type* a, size_type n, value_type* b)
{
  
  for (size_type i = 0u; i < n; ++i) {
    swap(a + i, b + i);
  }
}