#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

bool
equal(const value_type* a, size_type n, const value_type* b)
{
  return mismatch(a, n, b) == n;
}