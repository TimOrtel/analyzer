int foo2() {
    return 3;
}

int foo3() {
    return 3;
}

int fun1() {
    return foo2();
}

int fun2() {
    return foo3();
}

int main() {
    return fun1() + fun2();
}
