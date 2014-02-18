int mismatch(const int *a, int n, const int *b) 
{
for (int i = 0; i < n;)
//@ invariant 0 <= i && i <= n &*& ints(a, n, al) &*& ints(b, n, bl) &*& take(i, al) == take(i, bl);
{
    if (a[i] != b[i]) {   		
        return i;
    }
	
    //@ assert take(i, al) == take(i, bl);
    //@ assert nth(i, al) == nth(i, bl);
    //@ take_plus_one(i, al);
    //@ take_plus_one(i, bl);
    //@ assert take(i + 1, al) == append(take(i, al), cons(nth(i, al), nil));
    //@ assert take(i + 1, bl) == append(take(i, bl), cons(nth(i, bl), nil));
    i++;
    //@ assert take(i, al) == take(i, bl);
}
	
return n;
}
