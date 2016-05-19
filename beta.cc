#include <clay/array.h>

#include <algorithm>
#include <cstdlib>
#include <cstring>

clay_array_p chlore_beta_prefix(clay_array_p a1, clay_array_p a2) {
  clay_array_p prefix;
  int i, e;

  if (!a1 || !a2)
    return NULL;

  prefix = clay_array_malloc();
  for (i = 0, e = std::min(a1->size, a2->size); i < e && a1->data[i] == a2->data[i]; i++)
    ;
  if (prefix->size < i) {
    prefix->size = i;
    prefix->data = (int *) realloc(prefix->data, i * sizeof(int));
  }
  memcpy(prefix->data, a1->data, i * sizeof(int));
  return prefix;
}

