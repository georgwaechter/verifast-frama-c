// helper function to express that the list heads (of length n) are equal
/*@ fixpoint bool eq_ints(list<int> a, list<int> b, int n) {
    switch (a) {
        case cons(a0, ax): return n <= 0 ? true : switch (b) {
            case cons(b0, bx): return a0 == b0;
            case nil: return false;
        };
        case nil: return n <= 0 ? true : false;
    }
}
@*/

int mismatch(int *a, int* b, int size) 
//@ requires ints(a, size, ?al) &*& ints(b, size, ?bl) &*& size >= 0;
//@ ensures ints(a, size, al) &*& ints(b, size, bl) &*& result >= 0 && result <= size && eq_ints(al, bl, result - 1) == true && ((result < size) ? (nth(result, al) != nth(result, bl)) : true);
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    
    for (int i = 0; i < size; i++)
    //@ invariant i >= 0 && i <= size &*& eq_ints(al, bl, i) == true &*& ints(a, size, al) &*& ints(b, size, bl);
    {
    	if (a[i] != b[i])
    	{   		
    		return i;
    	}
    }
	
    return size;
}

void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {1, 2};
	int b[2] = {2, 1};

	int ret = mismatch(a, b, 2);
	assert(ret == 2);
}

