/*@
lemma_auto void ints_inv();
    requires ints(?p, ?count, ?vs);
    ensures ints(p, count, vs) &*& count == length(vs);
@*/