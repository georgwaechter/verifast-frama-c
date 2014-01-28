/*@
  requires \valid(a, 0..n-1);
  requires \valid(b, 0..n-1);
  requires n >= 0;
  assigns \nothing;
  ensures \result <==> IsEqual(a, n, b);
*/ 
bool equal(const int* a, int n, const int* b);