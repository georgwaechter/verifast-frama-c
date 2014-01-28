bool equal(const int* a, int n, const int* b)
//@ requires ints(a, n, ?al) &*& ints(b, n, ?bl) &*& n >= 0;
//@ ensures result == (al == bl) &*& ints(a, n, al) &*& ints(b, n, bl);
{
    //@ open ints(a, n, al);
    //@ open ints(b, n, bl);
    if (n == 0) {
    	return true;
    }
    
    if (*a != *b) {
    	return false;
    }
    
    return equal(a + 1, b + 1, n - 1);
}
     