/*
** Execute with
** gcc main.c
** make_coredump.sh config.snapshot a.out
** binsec -sse -isa amd64 -reflection -sse-script config.ini config.snapshot
*/

void error(char *msg);
int main() { error("Hello world!"); }
