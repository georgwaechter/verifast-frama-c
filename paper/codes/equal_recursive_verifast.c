bool equal(const int* a, int n, const int* b)
//@ requires ints(a, n, ?al) &*& ints(b, n, ?bl) &*& n >= 0;
//@ ensures result == (al == bl) &*& ints(a, n, al) &*& ints(b, n, bl);
{
    //@ open ints(a, n, al);
    //@ open ints(b, n, bl);
		
    if (n == 0) {
        //@ assert length(al) == 0 && length(bl) == 0;
        //@ assert al == bl;
        //@ close ints(a, n, al);
        //@ close ints(b, n, bl);
        return true;
    }
    
    // ...
}
     