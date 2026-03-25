#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
make_heap(value_type* a, size_type n)
{
  if (0u < n) {
    
    for (size_type i = 1u; i < n; ++i) {
      push_heap(a, i + 1u);

    }

  }

}