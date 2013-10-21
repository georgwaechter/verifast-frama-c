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

/*@ fixpoint int mismatch_ints(list<int> a, list<int> b) {
    switch (a) {
        case cons(a0, ax): return switch (b) {
            case cons(b0, bx): return a0 == b0 ? 1 + mismatch_ints(ax, bx) : 0;
            case nil: return 1;
        };
        case nil: return switch (b) {
            case cons(b0, bx): return 1;
            case nil: return 0;
        };
    }
}
@*/

/*@ lemma_auto void eq_mismatch_inverse(list<int> a, list<int> b, int n);
    requires eq_ints(a, b, n) == true;
    ensures mismatch_ints(a, b) >= n;
@*/


/*@ lemma_auto void eq_mismatch_inverse2(list<int> a, list<int> b, int n);
    requires nth(n, a) != nth(n, b);
    ensures mismatch_ints(a, b) <= n;
@*/

/*@ lemma_auto void eq_mismatch_inverse3(list<int> a, list<int> b);
    requires length(a) == length(b) && eq_ints(a, b, length(a)) == true;
    ensures mismatch_ints(a, b) == length(a);
@*/

int mismatch(int *a, int* b, int size) 
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
/*@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& 
            result == mismatch_ints(al, bl); @*/
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    
    for (int i = 0; i < size; i++)
    //@ invariant i >= 0 && i <= size &*& eq_ints(al, bl, i) == true &*& ints(a, size, al) &*& ints(b, size, bl);
    {
    	if (a[i] != b[i])
    	{   		
    		//@ assert mismatch_ints(al, bl) == i;
    		return i;
    	}
    }
    
    //@ assert mismatch_ints(al, bl) == size;
	
    return size;
}

void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {1, 2};
	int b[2] = {2, 1};

	int ret = mismatch(a, b, 2);
	assert(ret == 0);
}

