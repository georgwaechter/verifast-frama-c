/*@
 predicate IsEqual(int* a, integer n, int* b) =
   \forall integer i; 0 <= i < n ==> a[i] == b[i];
*/

/*@
  requires \valid_range(a, 0, n - 1);
  requires \valid_range(b, 0, n - 1);
  assigns \nothing;

  behavior all_equal:
    assumes IsEqual(a, n, b);
    ensures \result == n;

  behavior some_not_equal:
    assumes !IsEqual(a, n, b);
    ensures 0 <= \result < n;
    ensures a[\result] != b[\result];
    ensures IsEqual(a, \result, b);

  complete behaviors;
  disjoint behaviors;
*/
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