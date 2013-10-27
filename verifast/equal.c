/*@ lemma_auto void tail_length(list<int> a);
    requires length(a) > 0;
    ensures length(tail(a)) == length(a) - 1;
@*/
    

/*@ lemma_auto void inductive_equal_lists(list<int> a, list<int> b, int n)
    requires take(n, a) == take(n, b) &*& nth(n, a) == nth(n, b) && n >= 0;
    ensures take(n + 1, a) == take(n + 1, b);
    {
    	if (n == 0)
    	{
    	    return;
    	} 
        else
        { 
            inductive_equal_lists(a, b, n - 1); 
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
    //@ invariant i >= 0 && i <= size &*& take(i, al) == take(i, bl) &*& ints(a, size, al) &*& ints(b, size, bl);
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

