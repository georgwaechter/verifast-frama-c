/*@
lemma void take_plus_one<t>(int i, list<t> xs);
    requires 0 <= i && i < length(xs);
    ensures take(i + 1, xs) == append(take(i, xs), cons(nth(i, xs), nil));
@*/