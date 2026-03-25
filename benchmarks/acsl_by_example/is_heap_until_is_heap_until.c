#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
is_heap_until(const value_type* a, size_type n)
{
  size_type parent = 0u;

  for (size_type child = 1u; child < n; ++child) {
    if (a[parent] < a[child]) {
      return child;
    }

    if ((child % 2u) == 0u) {
      ++parent;
    }
  }

  return n;
}