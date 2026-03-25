#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
sort_heap(value_type* a, size_type n)
{
  
  for (size_type i = n; i > 1u; --i) {
    
    pop_heap(a, i);

  }

}