char *strdup(const char *s);
//@ requires string(s, ?length);
//@ ensures string(s, length) &*& string(result, length) &*& malloc_block_chars(result, length + 1);