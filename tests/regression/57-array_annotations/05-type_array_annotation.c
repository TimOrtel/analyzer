// PARAM: --set ana.base.arrays.unrolling-factor 4 --enable annotation.array

void t1(void) {
     __attribute__((goblint_array_domain("unroll")))int x[4] ;

    x[0] = 0;
    x[1] = 1;
    x[2] = 2;
    x[3] = 3;
    
    assert(x[0] == 0);
    assert(x[1] == 1);
    assert(x[2] == 2);
    assert(x[3] == 3);

}

typedef int unrollInt __attribute__((goblint_array_domain("unroll")));

void t2(void) {
    unrollInt x[4] ;

    x[0] = 0;
    x[1] = 1;
    x[2] = 2;
    x[3] = 3;
    
    assert(x[0] == 0);
    assert(x[1] == 1);
    assert(x[2] == 2);
    assert(x[3] == 3);

}

int main(void)
{
   t1();
   t2();
}
