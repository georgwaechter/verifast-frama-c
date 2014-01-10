/*@
 predicate IsEqual(value_type* a, integer n, value_type* b) =
   \forall integer i; 0 <= i < n ==> \at(a[i]) == \at(b[i]);
*/