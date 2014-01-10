/*@
  predicate int_array(int *start, int count) =
    count <= 0 ? true : integer(start, _) &*& int_array(start + 1, count - 1);
@*/