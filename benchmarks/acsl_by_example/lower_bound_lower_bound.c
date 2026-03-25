#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
lower_bound(const value_type* a, size_type n, value_type v)
{
  size_type left  = 0u;
  size_type right = n;

  while (left < right) {
    const size_type middle = left + (right - left) / 2u;

    if (a[middle] < v) {
      left = middle + 1u;
    }
    else {
      right = middle;
    }
  }

  return left;
}