#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

value_type
inner_product(const value_type* a, const value_type* b, size_type n,
              value_type init)
{
  
  for (size_type i = 0u; i < n; ++i) {
    
    init = init + a[i] * b[i];
  }

  return init;
}