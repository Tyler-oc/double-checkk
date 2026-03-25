#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
find4(const value_type* a, size_type n, value_type v)
{
  return find3(a, n, v);
}