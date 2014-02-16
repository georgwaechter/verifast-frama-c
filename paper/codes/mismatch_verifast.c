int mismatch(const int *a, int n, const int *b) 
{
    for (int i = 0; i < n; i++)
    //@ invariant 0 <= i && i <= n &*& ints(a, n, al) &*& ints(b, n, bl) &*& take(i, al) == take(i, bl);
    {
    	if (a[i] != b[i])
    	{   		
    	    return i;
    	}
    }
	
    return n;
}
