#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

void
swap(value_type* p, value_type* q)
{
  value_type save = *p;
  *p = *q;
  *q = save;
}