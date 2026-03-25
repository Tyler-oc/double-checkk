#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
partial_sum_inv(value_type* a, size_type n, value_type* b)
{
  partial_sum(a, n, b);
  adjacent_difference(b, n, a);
}