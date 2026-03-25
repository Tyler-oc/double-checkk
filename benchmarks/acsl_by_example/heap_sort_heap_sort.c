#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
heap_sort(value_type* a, size_type n)
{
  make_heap(a, n);
  sort_heap(a, n);
}