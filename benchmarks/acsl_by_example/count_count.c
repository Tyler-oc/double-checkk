#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
count(const value_type* a, size_type n, value_type v)
{
  size_type counted = 0u;

  for (size_type i = 0u; i < n; ++i) {
    if (a[i] == v) {
      counted++;
    }
  }

  return counted;
}