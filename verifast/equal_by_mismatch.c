#include "mismatch.h"

//@ #include "listex.gh"

bool equal(int *a, int* b, int size) 
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result == (al == bl);
{
    // split into two lines, because of undefined behavior in c spec (says verifast)
    int ret = mismatch(a, b, size);
    
    return ret == size;
}

void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {1, 2};
	int b[2] = {1, 2};

	bool ret = equal(a, b, 2);
	assert(ret == true);
	
	b[1] = 3;
	
	ret = equal(a, b, 2);
	assert(ret == false);
}
