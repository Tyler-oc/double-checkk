#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
reverse(value_type* a, size_type n)
{
  const size_type half = n / 2u;

  for (size_type i = 0u; i < half; ++i) {
    swap(&a[i], &a[n - 1u - i]);
  }
}