# Fixed 53/13 detector over varying compatible CM fields

[VARYING-CM-SAME-TEST-VECTOR.md](VARYING-CM-SAME-TEST-VECTOR.md) extends the [fixed level-2544 reference calculation](../heegner-odd2544-theta/) without changing its definite lattice, residue detector, or coefficient normalization. It proves the two-coefficient formula for any pair of parameters meeting the listed hypotheses. It does not calculate a new large coefficient or assert nonvanishing.

## Current arithmetic screen, not a linked input

The earlier compact scalar has literal index h=473592745039516333133760 and the original ordered β primes 5, 11, 17, 163, 661, 733, 1489, 1861. Of the companion squareclass θ, four distinct actual prime factors are currently certified: 131, 6551, 2470991 and 16782959. Their product is 13 mod 24, whereas θ is 1 mod 24, so the listed support is necessarily incomplete. Here are two necessary-only field screens for that same scalar:

| Prime m | Actual W mod m | Actual δ=1−b/17 mod m | One square root of δ mod m |
|---:|---:|---:|---:|
| 521879 | 199848 | 90460 | 118553 |
| 977831 | 237678 | 679949 | 273442 |

Both m are 23 mod 24, all eight β primes and all four known θ primes split in ℚ(√−m), and 53 is inert. For the separately certified actual depth at 53, W≡1 gives δ≡17=21² mod 53. This preserves the desired 53 sign if a linked companion is later constructed. None of these checks gives full θ splitting, an actual retained q₀, the selected squarefree n or its paired nθ, or the actual ring-class conductors c=d for those selected inputs. No even or odd production coefficient is inferred. The negative-index source A₋(d) is independent of m, so changing m cannot repair a zero residue of that fixed coefficient.

The small checker verifies the finite table, known-support and residue arithmetic:

```sh
python3 check_candidate_screens.py
sha256sum -c SHA256SUMS
```

To independently recalculate the W residues against the original fixed-scalar circuit, pass its source directory:

```sh
python3 check_candidate_screens.py /path/to/the/fixed-scalar-circuit
```

The optional replay reads `select_scalar_specialization.py` (SHA-256 `7a79cdebea31c9e70c261794db865886721164cb35c813e4cdd7f13f944acd91`) and the three modular evaluator definitions from `check_actual_scalar_modular.py` (`754c590dc7c117b0835143b55974d18bc5cc4f0048d8d339fc3e25fab73df421`). The exact earlier scalar and added factor proofs are respectively `ACTUAL-MATERIALIZED-SCALAR-SPECIALIZATION.md` (`28078bc4ef7af3cd784a9e54c5ad20210fa77cf0c4eba10a57c74ddcdff39b4e`) and `ACTUAL-TWO-ADDITIONAL-H-PRIMES.md` (`8a935badb895146d19c76b0300fa24e9e9b5c0e2f72d9e665fb56ca8e63c23b4`). This extension does not duplicate those sources or the reference coefficient computation.
