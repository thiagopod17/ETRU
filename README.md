# ETRU

A SageMath implementation of ETRU, an NTRU-like lattice cryptosystem built
over the Eisenstein integers Z[ω], as described in Jarvis and Nevins (2015).
The repo also implements an LLL/BKZ key-recovery attack on ETRU, including
May's dimension-reduction idea for cutting down the lattice before running
BKZ.

## Installation

Requires [SageMath](https://www.sagemath.org/). No package to install —
just load the `.sage` file from a Sage session or notebook:

```python
load('ETRU_codigo_final.sage')
```

## Usage

```python
load('ETRU_codigo_final.sage')

# ETRU parameters: ring degree n, small modulus p, large modulus q, density r
n, p, q, r = 50, 3, 128, 2/3

# key generation: f, Fp = private key; h = public key
f, Fp, h, Fq, g = key_gen(n, p, q, r)

message = RrandomPolyModb(p)
ciphertext = encrypt(message, h)
recovered = decrypt(ciphertext, f, Fp)
```

The attack is run from `ETRU_Attack_simulation_final.ipynb`, which loads
`ETRU_codigo_final.sage` (the notebook itself refers to it as
`ETRU_Funcoes.sage`, an older filename) and expects a pickle file of
ETRU keypairs, e.g. produced by `gen_key_database`. For each key it
builds the ETRU lattice from the public key, applies May's dimension
cut, runs BKZ, and checks whether the reduced basis reveals the
private key or one of its rotations.

## Functions

| Function | Description |
|---|---|
| `key_gen(n, p, q, r)` | Generates an ETRU keypair: private key `f`, `Fp` (inverse of `f` mod `p`) and public key `h` |
| `encrypt(message, publickey)` | Encrypts a message polynomial under an ETRU public key |
| `decrypt(ciphertext, f, Fp)` | Decrypts an ETRU ciphertext with the private key |
| `gen_key_database(n, p, q, qtd, t)` | Generates `qtd` ETRU keypairs and pickles them to disk |
| `randomPolyinLf(n, p, q, r)` | Samples a random `f` candidate (invertible mod `p` and `q`) used in key generation |
| `randomPolyinLg(n, p, q, r)` | Samples a random `g` polynomial used in key generation |
| `lattice_etru(publickey, q, n)` | Builds the ETRU/NTRU lattice basis matrix from a public key |
| `run_bkz(M, n, corte, block_size)` | Runs BKZ reduction on a lattice, optionally cut down via May's dimension-reduction idea |
| `run_attack_single_key(...)` | Runs the full lattice-attack pipeline (build lattice, cut, BKZ) on one key and returns the result |
| `buscar_chave(m_red, f, n)` | Checks whether the private key (or a rotation of it) appears in a BKZ-reduced basis |

Lower-level arithmetic in Z[ω] and Z[ω][x] (modular reduction, GCD,
extended Euclidean algorithm, polynomial division/inversion mod a
prime) lives in the same file and backs the functions above.

## Repository layout

- `ETRU_codigo_final.sage` — ETRU arithmetic over Z[ω], key generation,
  encryption and decryption.
- `ETRU_Attack_simulation_final.ipynb` — builds the ETRU lattice, applies
  May's dimension-reduction cut, runs BKZ, and checks whether the attack
  recovered the private key.

## Reference

1. Jarvis, K., Nevins, M. (2015). ETRU: NTRU over the Eisenstein integers. *Designs, Codes and Cryptography*, 74:219–242.
2. Nevins, M., KarimianPour, C., Miri, A. (2010). NTRU over rings beyond Z. *Designs, Codes and Cryptography*, 56:65–78.
3. Knuth, D. E. (1997). *The Art of Computer Programming*, vol. 2 (3rd ed.): Seminumerical Algorithms. Addison-Wesley.
4. May, A., Silverman, J. H. (2001). Dimension reduction methods for convolution modular lattices. *International Cryptography and Lattices Conference*. Springer.
5. Silva, A. M. C., do Rego Sousa, T., Carneiro, T. (2024). Cutting dimensions in the LLL attack for the ETRU post-quantum cryptosystem. SBSEG 2024.
