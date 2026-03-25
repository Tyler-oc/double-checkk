#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type_pair
equal_range2(const value_type* a, size_type n, value_type v)
{
  size_type first  = 0u;
  size_type middle = 0u;
  size_type last   = n;

  while (last > first) {
    middle = first + (last - first) / 2u;

    if (a[middle] < v) {
      first = middle + 1u;
    }
    else if (v < a[middle]) {
      last = middle;
    }
    else {
      break;
    }
  }

  if (first < last) {
    
    size_type left = first + lower_bound(a + first, middle - first, v);

    ++middle;
    
    size_type right = middle + upper_bound(a + middle, last - middle, v);

    return make_pair(left, right);
  }
  else {
    return make_pair(first, first);
  }
}