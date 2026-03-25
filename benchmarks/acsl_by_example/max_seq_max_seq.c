#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

value_type
max_seq(const value_type* p, size_type n)
{
  return p[max_element2(p, n)];
}