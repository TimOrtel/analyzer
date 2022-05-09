// PARAM: --set ana.activated[+] "'var_eq'"  --set ana.activated[+] "'symb_locks'"
#include <stdlib.h>
#include <pthread.h>

typedef struct { int myint; pthread_mutex_t mymutex; } mystruct;

void lock(mystruct *s) { pthread_mutex_lock(&s->mymutex); }
void unlock(mystruct *s) { pthread_mutex_unlock(&s->mymutex); }

void *foo(void *arg) {
  mystruct *s = (mystruct *) arg;

  lock(s);
  s->myint=s->myint+1; // NORACE
  unlock(s);

  return NULL;
}

int main() {
  mystruct *s = (mystruct *) malloc(sizeof(*s));
  pthread_mutex_init(&s->mymutex, NULL);

  pthread_t id1, id2;
  pthread_create(&id1, NULL, foo, s);
  pthread_create(&id2, NULL, foo, s);
  pthread_join(id1, NULL);
  pthread_join(id2, NULL);
}
