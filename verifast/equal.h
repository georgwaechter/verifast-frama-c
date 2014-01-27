#ifndef EQUAL_H
#define EQUAL_H

bool equal(const int *a, int size, const int* b);
//@ requires a[0..size] |-> ?al &*& b[0..size] |-> ?bl &*& size >= 0;
//@ ensures a[0..size] |-> al &*& b[0..size] |-> bl &*& result == (al == bl);

#endif