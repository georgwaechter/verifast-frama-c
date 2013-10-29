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

int mismatch(int *a, int* b, int size) 
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result <= size &*& take(result, al) == take(result, bl) &*& (result < size ? nth(result, al) != nth(result, bl) : true); 
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    
    for (int i = 0; i < size; i++)
    //@ invariant i >= 0 && i <= size &*& ints(a, size, al) &*& ints(b, size, bl) &*& take(i, al) == take(i, bl);
    {
    	if (a[i] != b[i])
    	{   		
    	    return i;
    	}
    	
    	//@ take_plus_one(i, al);
    	//@ take_plus_one(i, bl);
    }
	
    return size;
}

void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {2, 2};
	int b[2] = {2, 2};

	int ret = mismatch(a, b, 2);
	assert(ret == 2);
}

