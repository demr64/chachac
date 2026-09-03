#include "chachac.h"
#include <string.h>
#include <stdio.h>

static const uint32_t constants[CONSTANTS] = {
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

    //asserts help the WP solver by providing small subgoals to arrive at Qed faster.
    //we had 4 big ensures. It did not arrive at Qed because there are too many nested calls.
    //so when ensuring qr_b2 for example, WP will use the asserts as given for granted 
    //after proving them and not compute them again, like this:
    //@ ghost uint32_t a0 = *a, b0 = *b, c0 = *c, d0 = *d;
    *a += *b;
    //@ assert *a == qr_a1(a0, b0, c0, d0);
    *d ^= *a;
    *d = rotl32(*d, 16);
    //@ assert *d == qr_d1(a0, b0, c0, d0);
    *c += *d;
    //@ assert *c == qr_c1(a0, b0, c0, d0);
    *b ^= *c;
    *b = rotl32(*b, 12);
    //@ assert *b == qr_b1(a0, b0, c0, d0);
    
    //operations happen two times so we may structure the formalization as having 2 steps.
    *a += *b;
    *d ^= *a;
    *d = rotl32(*d, 8);
    *c += *d;
    *b ^= *c;
    *b = rotl32(*b, 7);
}

/*@
    predicate is_valid_range(uint32_t* a, integer n) =
        (0 <= n) && \valid(a+(0.. n-1));
*/
/*@
    requires is_valid_range(state, 16);
    requires \separated(state+(0..15));
    assigns state[0..15];
*/
void inner_block(uint32_t state[]) {
     quarter_round(&state[0], &state[4], &state[8], &state[12]);
     quarter_round(&state[1], &state[5], &state[9], &state[13]);
     quarter_round(&state[2], &state[6], &state[10], &state[14]);
     quarter_round(&state[3], &state[7], &state[11], &state[15]);
     quarter_round(&state[0], &state[5], &state[10], &state[15]);
     quarter_round(&state[1], &state[6], &state[11], &state[12]);
     quarter_round(&state[2], &state[7], &state[8], &state[13]);
     quarter_round(&state[3], &state[4], &state[9], &state[14]);
}

/*@
    requires is_valid_range(key, 8);
    requires is_valid_range(nonce, 3);
    requires is_valid_range(key_stream, 16);
    requires is_valid_range(state, 16);
    assigns state[0..15], key_stream[0..15];
*/
void chacha20_block(uint32_t key[], uint32_t counter, uint32_t nonce[], uint32_t key_stream[],
        uint32_t state[]) {

    /*@ loop invariant 0 <= i <= CONSTANTS;
        loop assigns i, state[0..3];
        loop variant CONSTANTS - i;
    */
    for(size_t i=0; i<CONSTANTS; i++)
        state[i] = constants[i];

    /*@ loop invariant 0 <= i <= KEYLEN;
        loop assigns i, state[4..12];
        loop variant KEYLEN - i;
    */
    for(size_t i=0; i<KEYLEN; i++)
        state[i+4] = key[i];

    state[12] = counter;

    /*@ loop invariant 0 <= i <= NONCE;
        loop assigns i, state[13..15];
        loop variant NONCE - i;
    */
    for(size_t i=0; i<NONCE; i++)
        state[i+13] = nonce[i];

    uint32_t init[STATESIZE];

    /*@ loop invariant 0 <= i <= STATESIZE;
        loop assigns i, init[0..15];
        loop variant STATESIZE - i;
    */
    for(size_t i=0; i<STATESIZE; i++)
        init[i] = state[i];

    //<><>><> cha cha dance <><><><>
    
    /*@ loop invariant 0 <= i <= ROUNDS;
        loop assigns i, state[0..15];
        loop variant ROUNDS - i;
    */
    for(size_t i=0; i<ROUNDS; i++)
        inner_block(state);

    /*@ loop invariant 0 <= i <= STATESIZE;
        loop assigns i, state[0..15], key_stream[0..15];
        loop variant STATESIZE - i;
    */
    for(size_t i=0; i<STATESIZE; i++) {
        state[i] += init[i];
        key_stream[i] = state[i];
    }
}

