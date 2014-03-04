#include "mismatch.h"

//@ #include "listex.gh"

/*@
lemma void take_plus_one_<t>(int i, list<t> xs)
    requires 0 <= i && i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
{
  switch (xs) {
    case nil: // never visited due to i < length(xs)
    case cons(x, xs0):
      if (i > 0) {
        take_plus_one_(i - 1, xs0);
        assert take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
      } else {
        assert take(1, xs) == append(take(0, xs), cons(nth(0, xs), nil));
      }
  }
}
@*/


int mismatch(const int *a, int n, const int* b) 
//@ requires a[0..n] |-> ?al &*& b[0..n] |-> ?bl;
/*@ ensures  a[0..n] |->  al &*& b[0..n] |->  bl &*& result <= n &*& 
             take(result, al) == take(result, bl) &*& 
             (result < n ? nth(result, al) != nth(result, bl) : true); 
@*/
{
    for (int i = 0; i < n; i)
    //@ invariant 0 <= i && i <= n &*& ints(a, n, al) &*& ints(b, n, bl) &*& take(i, al) == take(i, bl);
    {
    	if (a[i] != b[i])
    	{   		
    	    return i;
    	}
    	
    	//@ take_plus_one_(i, al);
    	//@ take_plus_one_(i, bl);
    }
	
    return n;
}

void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {2, 2};
	int b[2] = {2, 2};

	int ret = mismatch(a, 2, b);
	assert(ret == 2);
}

