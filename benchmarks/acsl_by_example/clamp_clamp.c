#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

value_type
clamp(value_type v, value_type lower, value_type upper)
{
  return (v < lower) ? lower : (upper < v) ? upper : v;
}