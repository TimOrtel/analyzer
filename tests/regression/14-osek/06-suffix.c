// SKIP PARAM: --set ana.activated "['base','threadid','threadflag','escape','fmode', 'OSEK', 'OSEK2', 'stack_trace_set','mallocWrapper']" --set ana.osek.oil 02-example.oil --set ana.osek.tasksuffix _func --set ana.osek.isrsuffix _func
// Option 'tramp' has been removed, we used to set --set ana.osek.tramp 06-suffix-tramp.h 
int x;
int y;
int z;
int t;

ISR( ii ) {
   GetResource(ri);
    z = 20;
   ReleaseResource(ri);
   return;
}


ISR( i) {
   GetResource(r);
   y++;
   x--;
   ReleaseResource(r);
   return;
}

TASK(t) {
   GetResource(ri);
   x=10;
   y=0;
   ReleaseResource(ri);
   GetResource(r);
   t=x+y;
   x=t-x;
   ReleaseResource(r);
   z= 2*t; //RACE
   GetResource(r);
   y=t-y;
   ReleaseResource(r);
   TerminateTask();
return;}
