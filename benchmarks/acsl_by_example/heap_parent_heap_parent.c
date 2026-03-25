#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type
heap_parent(size_type child)
{
  return (0u < child) ?  (child - 1u) / 2u : 0u;
}