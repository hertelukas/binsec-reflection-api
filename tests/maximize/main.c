#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

size_t maximize(void *sym_var, size_t length) { exit(1); }
void *new_sym_var(size_t length) { exit(1); }

int main() {
  void *sym_var = new_sym_var(64);

  // Unconstrained
  printf("%zx", maximize(sym_var, 64));

  if (*(size_t *)sym_var < 0x80000000) {
    // Constrained
    printf("%zx", maximize(sym_var, 64));
  }
}
