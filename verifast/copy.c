//@ #include "listex.gh"

void copy(int *from, int size, int *to)
//@ requires from[0..size] |-> ?cont &*& to[0..size] |-> ?cont2 &*& size >= 0;
//@ ensures from[0..size] |-> cont &*& to[0..size] |-> cont;
{
    for (int i = 0; i < size; i++)
    //@ invariant from[0..size] |-> cont &*& to[0..size] |-> cont2 &*& take(i, cont) == take(i, cont2) &*& i <= size &*& 0 <= i;
    {
        to[i] = from[i];
        //@ take_plus_one(i, cont);
        //@ take_plus_one(i, cont2);
    }
}

void test() 
//@ requires true;
//@ ensures true;
{
	int a[2] = {1, 2};
	int b[2] = {0, 0};

	copy(a, 2, b);
	assert(b[0] == 1);
	assert(b[1] == 2);
}

