#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
find5(const value_type* a, size_type n, value_type v)
{
  return find2(a, n, v);
}