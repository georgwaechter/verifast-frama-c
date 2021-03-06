
// verifast is not able to conclude on its own that a list with length zero = nil
/*@
lemma_auto void length_nil<t>(list<t> xs);
    requires length(xs) == 0;
    ensures xs == nil;
@*/

bool equal_ints2(int *a, int *b) 
//@ requires ints(a, 2, ?al) &*& ints(b, 2, ?bl);
//@ ensures ints(a, 2, al) &*& ints(b, 2, bl) &*& result == (al == bl);
{
	//@ open ints(a, 2, al);
	//@ open ints(b, 2, bl);
	if (a[0] != b[0])
	{
		//@ assert al != bl;
		return false;
	}
	
	//@ open ints(a + 1, 1, ?af);
	//@ open ints(b + 1, 1, ?bf);
	if (a[1] != b[1]) {
		return false;
	}
	
	// due to the lemma (see above) verifast is able to conclude that
	// af == bf at this point - and thus al == bl
	// (without the lemma verifast cant prove that the zero length tais are identical)
			
	return true;
}


void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {1, 2};
	int b[2] = {1, 2};

	bool ret = equal_ints2(a, b);
	assert(ret == true);
}

