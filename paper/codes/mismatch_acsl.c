int mismatch(const int *a, int n, const int *b) {
    /*@
      loop invariant 0 <= i <= n;
      loop invariant IsEqual(a, i, b);
      loop assigns i;
    */
    for (int i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return i;
        }
    }
	
    return n;
}