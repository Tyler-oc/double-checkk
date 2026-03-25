#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

bool
is_heap(const value_type* a, size_type n)
{
  return is_heap_until(a, n) == n;
}