#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void rewrite_array(value_type* a, size_type n)
{
  
  for (size_type i = 0u; i < n; i++) {
    a[i] = a[i];
  }
}