/*
** Execute with
** gcc main.c
** make_coredump.sh config.snapshot a.out
** binsec -sse -isa amd64 -reflection -sse-script config.ini config.snapshot
*/
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

size_t minimize(void *sym_var, size_t length) { exit(1); }
void *new_sym_var(size_t length) { exit(1); }

int main() {
  void *sym_var = new_sym_var(64);

  // Unconstrained
  printf("%zx", minimize(sym_var, 64));

  if (*(size_t *)sym_var == UINT64_MAX) {
    printf("%zx", minimize(sym_var, 64));
  } else if ((*(size_t *)sym_var) * 2 < 1) {
    printf("%zx", minimize(sym_var, 64));
  } else if (*(size_t *)sym_var > 0x80000001) {
    printf("%zx", minimize(sym_var, 64));
  } else if (*(size_t *)sym_var > 0x80000000) {
    printf("%zx", minimize(sym_var, 64));
  } else if (*(size_t *)sym_var > 0x7fffffff) {
    printf("%zx", minimize(sym_var, 64));
  } else if (*(size_t *)sym_var > 0x7ffffffe) {
    printf("%zx", minimize(sym_var, 64));
  }
}
