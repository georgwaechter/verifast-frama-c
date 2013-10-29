/*@ 
// copied from listex.h
lemma void take_plus_one<t>(int i, list<t> xs)
    requires 0 <= i &*& i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            if (i != 0) {
                take_plus_one(i - 1, xs0);
            }
    }
}
@*/

bool equal(int *a, int* b, int size) 
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result == (al == bl);
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    for (int i = 0; i < size; i++)
    //@ invariant 0 <= i && i <= size &*& ints(a, size, al) &*& ints(b, size, bl) &*& take(i, al) == take(i, bl);
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

	bool ret = equal(a, b, 2);
	assert(ret == true);
	
	b[1] = 3;
	
	ret = equal(a, b, 2);
	assert(ret == false);
}

