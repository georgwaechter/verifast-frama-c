/*@
  requires \valid(a+(0.. n-1));
  requires \valid(b+(0.. n-1));
  requires n >= 0;
  assigns \nothing;
  ensures \result <==> \forall integer i; 0 <= i < n ==> \at(a[i]) == \at(b[i]);
*/ 
bool equal(const int* a, int n, const int* b);