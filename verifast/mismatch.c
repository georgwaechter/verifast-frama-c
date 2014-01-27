#include "mismatch.h"

//@ #include "listex.gh"

int mismatch(const int *a, int n, const int* b) 
//@ requires a[0..n] |-> ?al &*& b[0..n] |-> ?bl &*& n >= 0;
//@ ensures a[0..n] |-> al &*& b[0..n] |-> bl &*& result <= n &*& take(result, al) == take(result, bl) &*& (result < n ? nth(result, al) != nth(result, bl) : true); 
{
    //@ open ints(a, n, al);
    //@ open ints(b, n, bl);
    
    for (int i = 0; i < n; i++)
    //@ invariant i >= 0 && i <= n &*& ints(a, n, al) &*& ints(b, n, bl) &*& take(i, al) == take(i, bl);
    //@ decreases n - i;
    {
    	if (a[i] != b[i])
    	{   		
    	    return i;
    	}
    	
    	//@ take_plus_one(i, al);
    	//@ take_plus_one(i, bl);
    }
	
    return n;
}

void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {2, 2};
	int b[2] = {2, 2};

	int ret = mismatch(a, 2, b);
	assert(ret == 2);
}

