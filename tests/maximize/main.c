/*
** Execute with
** gcc main.c
** make_coredump.sh config.snapshot a.out
** binsec -sse -isa amd64 -reflection -sse-script config.ini config.snapshot
*/
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

size_t maximize(void *sym_var, size_t length) { exit(1); }
void *new_sym_var(size_t length) { exit(1); }

int main() {
  size_t sym_var = (size_t)new_sym_var(64);

  // Unconstrained
  printf("%zx", maximize(&sym_var, 64));

  // Else if, so we do not analyze combinations of if statements
  if (sym_var == 0) {
    // Here, we can only have the solution 0
    printf("%zx", maximize(&sym_var, 64));
  } else if (sym_var * 2 < 1) {
    // This returns 0x8000000000000000, as 2 * that = 0
    printf("%zx", maximize(&sym_var, 64));
  } else if (sym_var < 0x7FFFFFFF) {
    // And step through a couple of adjacent numbers
    printf("%zx", maximize(&sym_var, 64));
  } else if (sym_var < 0x80000000) {
    printf("%zx", maximize(&sym_var, 64));
  } else if (sym_var < 0x80000001) {
    printf("%zx", maximize(&sym_var, 64));
  }
}
