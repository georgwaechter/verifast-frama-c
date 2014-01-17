/*@
  requires IsValidRange(a, n);
  requires IsValidRange(b, n);

  assigns \nothing;

  behavior all_equal:
    assumes \forall integer i; 0 <= i < n ==> a[i] == b[i];
    ensures \result;

  behavior some_not_equal:
    assumes \exists integer i; 0 <= i < n && a[i] != b[i];
    ensures !\result;

  complete behaviors;
  disjoint behaviors;
*/
bool equal(const int* a, int n, const int* b);