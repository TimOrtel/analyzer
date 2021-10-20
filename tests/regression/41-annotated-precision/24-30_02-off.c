// PARAM: --set solver td3 --enable exp.partition-arrays.enabled --set ana.activated "['base','threadid','threadflag','escape','expRelation','mallocWrapper']" --set exp.privatization none --disable exp.fast_global_inits --disable ana.int.def_exc --enable exp.annotated.precision --set ana.int.refinement fixpoint
// This checks that partitioned arrays and fast_global_inits are no longer incompatible
int global_array[50];
int global_array_multi[50][2][2];

int main(void) __attribute__((goblint_precision("interval"))) {
  for(int i =0; i < 50; i++) {
      assert(global_array[i] == 0);
      assert(global_array_multi[i][1][1] == 0);
  }
}
