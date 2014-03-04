bool equal(const int *a, int n, const int* b);
//@ requires a[0..n] |-> ?al &*& b[0..n] |-> ?bl &*& size >= 0;
//@ ensures a[0..n] |-> al &*& b[0..n] |-> bl &*& result == (al == bl);