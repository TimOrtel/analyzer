// PARAM: --set ana.activated[+] "'octApron'" --enable dbg.debug --enable ana.int.interval

int main(void) {
    int x, y, r;
    x = 5;
    assert(x == 3); // FAIL
    assert(x == 5); 
    y = 3;
    r = x + y;
    while (x != y) {
        assert(r > 0); 
        if (y > x) 
            y = y - x;
        else 
            x = x - y;
        assert(r > x + y);
        r = x + y; 
    }
    return 0;
}