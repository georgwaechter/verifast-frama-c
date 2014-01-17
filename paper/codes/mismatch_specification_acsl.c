/*@
  requires IsValidRange(a, n);
  requires IsValidRange(b, n);
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
int mismatch(const int *a, int n, const int *b);