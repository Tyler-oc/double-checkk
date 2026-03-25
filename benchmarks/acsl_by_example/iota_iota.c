#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
iota(value_type* a, size_type n, value_type v)
{
  
  for (size_type i = 0u; i < n; ++i) {
    a[i] = v++;
  }
}