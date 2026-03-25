#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type_pair
equal_range(const value_type* a, size_type n, value_type v)
{
  size_type first  = lower_bound(a, n, v);
  size_type second = upper_bound(a, n, v);
  
  return make_pair(first, second);
}