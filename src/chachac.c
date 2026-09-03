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

/*@ logic uint32_t rotl(uint32_t x, integer n) =
        (uint32_t)((x << n) | (x >> (32 - n)));
*/
/*@ requires 0 <= n <= 31;
    assigns \nothing;

    behavior zero:
        assumes n == 0;
        ensures \result == x;
    behavior nonzero:
        assumes n > 0;
        ensures \result == rotl(x, n);

    complete behaviors;
    disjoint behaviors;
*/
uint32_t rotl32(uint32_t x, unsigned int n) {
    if(n == 0) 
        return x;
    return (x << n) | (x >> (32 - n));
}

//why did I make this
/*@
    logic uint32_t xor(uint32_t x, uint32_t y, integer n) = rotl((uint32_t)(x ^ y), n);
    logic uint32_t sum(uint32_t x, uint32_t y) = (uint32_t)(x + y);
    
    logic uint32_t qr_a1(uint32_t a, uint32_t b, uint32_t c, uint32_t d) =
        sum(a, b);
    logic uint32_t qr_d1(uint32_t a, uint32_t b, uint32_t c, uint32_t d) =
        xor(d, qr_a1(a, b, c, d), 16);

    logic uint32_t qr_c1(uint32_t a, uint32_t b, uint32_t c, uint32_t d) =
        sum(c, qr_d1(a, b, c, d));

    logic uint32_t qr_b1(uint32_t a, uint32_t b, uint32_t c, uint32_t d) =
        xor(b, qr_c1(a, b, c, d), 12);


    logic uint32_t qr_a2(uint32_t a, uint32_t b, uint32_t c, uint32_t d) =
        sum(qr_b1(a, b, c, d), qr_a1(a, b, c, d));

    logic uint32_t qr_d2(uint32_t a, uint32_t b, uint32_t c, uint32_t d) =
        xor(qr_d1(a, b, c, d), qr_a2(a, b, c, d), 8);

    logic uint32_t qr_c2(uint32_t a, uint32_t b, uint32_t c, uint32_t d) =
        sum(qr_c1(a, b, c, d), qr_d2(a, b, c, d));


    logic uint32_t qr_b2(uint32_t a, uint32_t b, uint32_t c, uint32_t d) =
        xor(qr_b1(a, b, c, d), qr_c2(a, b, c, d), 7);
*/


/*@ requires \valid(a) && \valid(b) && \valid(c) && \valid(d);
    requires \separated(a,b,c,d);
    assigns *a, *b, *c, *d;
    ensures *a == qr_a2(\old(*a), \old(*b), \old(*c), \old(*d));
    ensures *b == qr_b2(\old(*a), \old(*b), \old(*c), \old(*d));
    ensures *c == qr_c2(\old(*a), \old(*b), \old(*c), \old(*d));
    ensures *d == qr_d2(\old(*a), \old(*b), \old(*c), \old(*d));
*/
void quarter_round(uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d) {
    *a += *b;
    *d ^= *a;
    *d = rotl32(*d,16);

    *c += *d;
    *b ^= *c;
    *b = rotl32(*b,12);
    //operations happen two times so we may formalize them in frama like that.
    *a += *b;
    *d ^= *a;
    *d = rotl32(*d,8);
    
    *c += *d;
    *b ^= *c;
    *b = rotl32(*b,7);
}


/*@ assigns \nothing; */
int main() {
    return 0;
}
