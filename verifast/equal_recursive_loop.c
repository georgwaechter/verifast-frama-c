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
    bool ret = true;
	
    while (true)
    //@ requires a[i..size] |-> drop(i, al) &*& b[i..size] |-> drop(i, bl) &*& size >= 0;
    //@ ensures a[old_i..size] |-> drop(i, al) &*& b[old_i..size] |-> drop(i, bl) &*& ret == (drop(i, al) == drop(i, bl));
    {
        ret = true;
        
        if (i == size)
        {
            break;
        }
    	
        //@ open ints(a + i, size - i, drop(i, al));
        //@ open ints(b + i, size - i, drop(i, bl));
    	if (a[i] != b[i])
    	{   		
    	    ret = false;
	    break;
    	}

    	i++;
    	//@ recursive_call();
    }

    return ret;
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

