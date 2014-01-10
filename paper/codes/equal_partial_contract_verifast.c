bool equal(const int *a, int n, const int* b);
//@ requires int_array(a, n) &*& int_array(b, n);
//@ ensures int_array(a, n) &*& int_array(b, n);