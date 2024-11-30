// Definition taken from PerformanceDatasets/LibcSummaries/api.c
#define symbolic void *

typedef unsigned int size_t;

/**
 * error - Terminate symbolic execution and print <msg>
 *
 * @msg: message to be outputted
 */
void error(char *msg) { return; }

/**
 * is_symbolic - Verifies if concatenation of <length> bits
 * starting from address of sym_var is symbolic

 * @sym_var: Address of simbolic variable
 * @length: Size in bits
 *
 * Returns 1 if is symbolic,
 *          0 otherwise
 */
int is_symbolic(symbolic sym_var, size_t length) {
  error("API function: is_symbolic() not implemented");
  return 0;
}

int main(int argc, char *argv[]) {
  is_symbolic(argv, 8);
  return 0;
}
