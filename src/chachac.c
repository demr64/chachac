#include "chachac.h"
#include <string.h>
#include <stdio.h>
#define STATESIZE 16
#define ROUNDS 10

static uint32_t state[STATESIZE];

static const uint32_t constants[4] = {
    0x61707865, 0x3320646e,
    0x79622d32, 0x6b206574
};

/*@ requires 0 <= n <= 31;
    assigns \nothing;

    behavior zero:
        assumes n == 0;
        ensures \result == x;
    behavior nonzero:
        assumes n > 0;
        ensures \result == (uint32_t)((x << n) | (x >> (32 - n)));

    complete behaviors;
    disjoint behaviors;
*/

uint32_t rotl32(uint32_t x, unsigned int n) {
    if(n == 0) 
        return x;
    return (x << n) | (x >> (32 - n));
}

/*@ assigns \nothing; */
int main() {
    return 0;
}
