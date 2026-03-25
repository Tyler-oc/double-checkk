#include <stddef.h>
#include <stdbool.h>
typedef size_t size_type;
typedef int value_type;

size_type_pair
make_pair(size_type first, size_type second)
{
  size_type_pair pair;

  pair.first  = first;
  pair.second = second;

  return pair;
}