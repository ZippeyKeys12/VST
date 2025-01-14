#include "lock.h"

lock_t* makelock(void) {
    return make_atomic(1);
}

void freelock(lock_t *lock) {
    free_atomic(lock);
}

void acquire(lock_t *lock) {
    int b = 0;
    int expected;
    do {
        expected = 0;
        b = atom_CAS(lock, &expected, 1);
    } while (b == 0);
}

void release(lock_t *lock) {
    atom_store(lock, 0);
}
