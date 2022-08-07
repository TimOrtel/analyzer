int foo() {
    return 3;
}

int fun1() {
    return foo();
}

int fun2() {
    return foo();
}

int main() {
    return fun1() + fun2();
}
