/*@
  requires \valid(a+(0.. n-1));
  requires \valid(b+(0.. n-1));
  requires n >= 0;

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