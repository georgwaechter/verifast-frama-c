/*@
lemma void take_plus_one<t>(int i, list<t> xs)
    requires 0 <= i && i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
{
  switch (xs) {
    case nil: // wird nie betrachtet, da i < length(xs)
    case cons(x, xs0):
      if (i > 0) {
        take_plus_one(i - 1, xs0);
        assert take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
      } else {
        assert take(1, xs) == append(take(0, xs), cons(nth(0, xs), nil));
      }
  }
}
@*/