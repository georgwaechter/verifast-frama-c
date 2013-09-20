/*@
   predicate int_array(int *s, int size; list<int> ci) =
    size == 0 ? ci == nil : integer(s, ?v) &*& int_array(s + 1, size - 1, ?ci0) &*& ci == cons(v, ci0);
@*/

/*@ fixpoint bool equal_int_lists(list<int> a, list<int> b) {
        switch(a) {
            case nil: return true;
            case cons(av, at): return switch (b) {
                case nil: return false;
                case cons(bv, bt): return av == bv && equal_int_lists(at, bt);
            };
        }
    }
@*/


int mismatch_int_array(int* a, int* b, int size)
//@ requires int_array(a, size, ?al) &*& int_array(b, size, ?bl) &*& size >= 0;
//@ ensures equal_int_lists(al, bl) ? result == 0 : result == 1 &*& int_array(a, size, al) &*& int_array(b, size, bl);
{
    //@ open int_array(a, size, al);
    //@ open int_array(b, size, bl);
    
    if (size == 0) {
    	return 0;
    }
    
    int av = *a;
    int bv = *b;
    
    if (av != bv) {
    	return 1;
    }
    
    int t = mismatch_int_array(a + 1, b + 1, size - 1);
    
    // TODO: fix leaking (first entries of both arrays seem to be missing)
    // @ open int_array(a + 1, size - 1, tail(al));
    // @ close int_array(a, size, al);
    // same for b ...
    
    return t;
}
     

int equal_int_array(int* a, int* b, int size)
//@ requires int_array(a, size, ?al) &*& int_array(b, size, ?bl) &*& size >= 0;
//@ ensures equal_int_lists(al, bl) ? result == 1 : result == 0 &*& int_array(a, size, al) &*& int_array(b, size, bl);
{
    //@ open int_array(a, size, al);
    //@ open int_array(b, size, bl);
    
    if (size == 0) {
    	return 1;
    }
    
    int av = *a;
    int bv = *b;
    
    if (av != bv) {
    	return 0;
    }
    
    int t = equal_int_array(a + 1, b + 1, size - 1);
    
    return t;
}
     