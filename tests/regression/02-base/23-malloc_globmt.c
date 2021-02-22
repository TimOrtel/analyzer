// PARAM: --set ana.activated "['base','threadid','threadflag','escape','mallocWrapper']"
#include <stdlib.h>
#include <pthread.h>
#include <assert.h>

int *x;
int *y;

void *t_fun(void *arg) {
  *x = 3;
  return NULL;
}

int main() {
  pthread_t id;

  x = malloc(sizeof(int));
  y = malloc(sizeof(int));

  *x = 0;
  *y = 1;

  assert(*x == 0); // UNKNOWN
  assert(*y == 1); // UNKNOWN

  pthread_create(&id, NULL, t_fun, NULL);

  assert(*x == 0); // UNKNOWN
  assert(*y == 1); // UNKNOWN

  return 0;
}
