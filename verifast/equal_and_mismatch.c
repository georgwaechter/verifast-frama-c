
bool not_equal_int_array(int* a, int* b, int size)
//@ requires ints(a, size, ?al) &*& ints(b, size, ?bl) &*& size >= 0;
//@ ensures result == (al != bl) &*& ints(a, size, al) &*& ints(b, size, bl);
{
    //@ open ints(a, size, al);
    //@ open ints(b, size, bl);
    
    if (size == 0) {
    	return false;
    }
    
    int av = *a;
    int bv = *b;
    
    if (av != bv) {
    	return true;
    }
    
    bool t = not_equal_int_array(a + 1, b + 1, size - 1);
    
    // TODO: fix leaking (first entries of both arrays seem to be missing)
    // @ open int_array(a + 1, size - 1, tail(al));
    // @ close int_array(a, size, al);
    // same for b ...
    
    return t;
}
     

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
     