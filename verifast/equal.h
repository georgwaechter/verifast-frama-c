#ifndef EQUAL_H
#define EQUAL_H

typedef bool equal(int *a, int* b, int size);
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result == (al == bl);

#endif