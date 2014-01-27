#include "equal.h"

//@ #include "listex.gh"

bool equal(const int *a, int size, const int* b) 
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result == (al == bl);
{

    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    for (int i = 0; i < size; i++)
    //@ invariant 0 <= i && i <= size &*& ints(a, size, al) &*& ints(b, size, bl) &*& take(i, al) == take(i, bl);
    //@ decreases size - i;
    {
    	if (a[i] != b[i])
    	{   		
    	    return false;
    	}
    	
    	//@ take_plus_one(i, al);
    	//@ take_plus_one(i, bl);
    }

    return true;
}

void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {1, 2};
	int b[2] = {1, 2};

	bool ret = equal(a, 2, b);
	assert(ret == true);
	
	b[1] = 3;
	
	ret = equal(a, 2, b);
	assert(ret == false);
}

