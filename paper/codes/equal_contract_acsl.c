/*@
  requires IsValidRange(a, n);
  requires IsValidRange(b, n);
  assigns \nothing;
  ensures \result <==> IsEqual(a, n, b);
*/ 
bool equal(const int* a, int n, const int* b);