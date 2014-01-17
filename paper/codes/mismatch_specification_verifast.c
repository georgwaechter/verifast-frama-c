int mismatch(const int *a, int n, const int* b) ;
//@ requires a[0..n] |-> ?al &*& b[0..n] |-> ?bl &*& n >= 0;
//@ ensures a[0..n] |-> al &*& b[0..n] |-> bl &*& result <= n &*& take(result, al) == take(result, bl) &*& (result < n ? nth(result, al) != nth(result, bl) : true); 