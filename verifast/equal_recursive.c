
bool equal_int_array(int* a, int* b, int size)
//@ requires ints(a, size, ?al) &*& ints(b, size, ?bl) &*& size >= 0;
//@ ensures result == (al == bl) &*& ints(a, size, al) &*& ints(b, size, bl);
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    
    if (size == 0) {
    	return true;
    }
    
    int av = *a;
    int bv = *b;
    
    if (av != bv) {
    	return false;
    }
    
    bool t = equal_int_array(a + 1, b + 1, size - 1);
    
    return t;
}
     