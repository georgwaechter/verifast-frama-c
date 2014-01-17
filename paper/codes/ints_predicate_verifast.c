/*@
  predicate ints(int* start, int count, list<int> intlist) =
    count <= 0 ? intlist == nil : integer(start, ?value) &*& ints(start + 1, count - 1, ?tail) &*& intlist == cons(value, tail);
@*/