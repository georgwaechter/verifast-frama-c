

bool equal(int *a, int* b, int size) 
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result == (al == bl);
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    int i = 0;
    
    while (i < size)
    //@ invariant a[0..i] |-> ?alx &*& b[0..i] |-> ?blx &*& alx == blx && 0 <= i &*& ints(a, size, al) &*& ints(b, size, bl);
    {
    	if (a[i] != b[i])
    	{   		
    	    return false;
    	}
    	
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

