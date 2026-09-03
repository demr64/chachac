# chachac 
chachac is an implementation of theChaCha20 encryption algorithm, formally verified using the <a href="https://datatracker.ietf.org/doc/html/rfc8439">RFC 8439</a> and <a href="https://www.frama-c.com/">ACSL/Frama-C</a>.

# Introduction

### ChaCha20?
ChaCha20 is a symmetric encryption algorithm, successor of Salsa20, this algorithm is a good alternative to the more famous AES since it uses much less advanced mathematics using an ARX design (add, rotate, xor).
ChaCha20's internal state is based on a 4x4 array of 32-bits integers. The first four are constants, the next eight are a 256-bit key, then a 32-bit counter which increments in every operation, and a 96-bit nonce. This implementation for now focuses trying to prove mainly the internal block function.

## Verification

The current effort aims to show:
- memory safety
- correctness of the block function with respect to RFC 8439

It does **not** prove cryptographic security or the mathematical correctness of ChaCha20 as an encryption scheme.

## Installation & usage
Clone this repository:
```Bash
git clone https://github.com/demr64/chachac.git
cd chachac
```
You can verify the results my running:
```bash
make check
```
and run the official testcase running:
```Bash
make run
```

## License

MIT License

See [LICENSE](LICENSE) for more details.
