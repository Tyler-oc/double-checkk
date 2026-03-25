#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
adjacent_difference_inv(value_type* a, size_type n, value_type* b)
{
  adjacent_difference(a, n, b);
  partial_sum(b, n, a);
}