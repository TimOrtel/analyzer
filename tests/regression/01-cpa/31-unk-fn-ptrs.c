// PARAM: --set ana.activated "['base','threadid','threadflag','escape','mallocWrapper']"
extern void f_everything_up();

struct s {
	void (*f)(void);
	int data;
} s;

void hello(){
	//is it me your looking for ...
	assert(1);
}

int g = 0;
void (*fp)(void) = &hello;

int main(){
	s.f = &hello;
	assert(s.f == &hello); // UNKNOWN
	assert(fp == &hello); // UNKNOWN
	f_everything_up();
	s.f();
	assert(s.data == 0); // UNKNOWN!!1!one!
	assert(fp == &hello);// UNKNOWN
	return 0;
}
