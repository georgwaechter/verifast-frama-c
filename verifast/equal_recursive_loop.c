#include "equal.h"

//@ #include "listex.gh"

// this approach does not work, because verifast does not support requires-ensures loop with return statements
bool equal(int *a, int* b, int size) 
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result == (al == bl);
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    int i = 0;
    while (i < size)
    //@ requires a[i..size] |-> ?ali &*& b[i..size] |-> ?bli &*& size >= 0;
    //@ ensures a[old_i..size] |-> ?ali2 &*& b[old_i..size] |-> ?bli2 &*& ali2 == bli2;
    {
        //@ open ints(a + i, size - i, ali);
        //@ open ints(b + i, size - i, bli);
    	if (a[i] != b[i])
    	{   		
    	    return false;
    	}

    	i++;
    	//@ recursive_call();
    }

    return true;
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

