/*@
  predicate IsEqual(int* a, int n, int *b) =
    n <= 0 ? true : integer(a, ?av) &*& integer(b, ?bv) &*& (av == bv) &*& IsEqual(a + 1, n - 1, b + 1);
@*/

bool equal(const int *a, int size, const int* b) 
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& IsEqual(a, size, b);
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

