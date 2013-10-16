
// state that equal lists of the same size are the same
/*@ lemma_auto void eq_lists_detect(list<int> a, list<int> b);
    requires length(a) == length(b) && eq_ints(a, b, length(a));
    ensures a == b;
@*/

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

bool equal(int *a, int* b, int size) 
//@ requires ints(a, size, ?al) &*& ints(b, size, ?bl) &*& size >= 0;
//@ ensures ints(a, size, al) &*& ints(b, size, bl) &*& result == (al == bl);
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    
    for (int i = 0; i < size; i++)
    //@ invariant i >= 0 && i <= size &*& eq_ints(al, bl, i) == true &*& ints(a, size, al) &*& ints(b, size, bl);
    {
    	if (a[i] != b[i])
    	{   		
    		return false;
    	}
    }
	
	// the lemma (see above) helps to conclude al == bl
	// while assuming eq_ints(al, bl, size) - derived by the loop invariant
	// TODO: is it possible to verify the algorithm without fixpoints functions and lemmas?
    
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
}

