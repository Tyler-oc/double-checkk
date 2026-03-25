#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
selection_sort(value_type* a, size_type n)
{
  
  for (size_type i = 0u; i < n; ++i) {
    const size_type sel = i + min_element(a + i, n - i);

    if (i < sel) {
      
      swap(a + sel, a + i);
      
    }

  }

}