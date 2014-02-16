int mismatch(const int *a, int n, const int *b) {
    /*@
      loop invariant 0 <= i <= n;
      loop variant n - i;
      loop assigns i;
      loop invariant IsEqual(a, i, b);
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return i;
        }
    }
	
    return n;
}