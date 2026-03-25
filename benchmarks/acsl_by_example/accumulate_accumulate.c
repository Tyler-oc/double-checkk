#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

value_type
accumulate(const value_type* a, size_type n, value_type init)
{
  
  for (size_type i = 0u; i < n; ++i) {
    
    init = init + a[i];
  }

  return init;
}