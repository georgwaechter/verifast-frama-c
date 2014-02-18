/*@
  loop invariant 0 <= i <= n;
  loop invariant IsEqual(a, i, b);
  loop variant n - i;
  loop assigns i;
*/
for (int i = 0; i < n; i++) {
...
