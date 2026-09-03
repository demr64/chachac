#include <stdint.h>
#include <stdlib.h>
#define STATESIZE 16
#define CONSTANTS 4
#define KEYLEN 8
#define NONCE 3
#define ROUNDS 10


uint32_t rotl32(uint32_t x, unsigned int n);
void quarter_round(uint32_t *a, uint32_t *b, uint32_t *c, uint32_t *d);
void inner_block(uint32_t state[]);
void chacha20_block(uint32_t key[], uint32_t counter, uint32_t nonce[], uint32_t key_stream[], uint32_t state[]);
