#ifndef MISMATCH_H
#define MISMATCH_H

int mismatch(int *a, int* b, int size);
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result <= size &*& take(result, al) == take(result, bl) &*& (result < size ? nth(result, al) != nth(result, bl) : true); 

#endif