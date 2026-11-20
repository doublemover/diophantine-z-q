# Compatible CM field and an exact arithmetic gate for q₀

The checked constructions in this directory refer to the same fixed compact a=0 scalar. They do not require the caller to provide the list of prime factors of its squareclass θ.

1. [Actual scalar input](ACTUAL-MATERIALIZED-SCALAR-SPECIALIZATION.md): the fixed index, exact labels and compact rational δ=1−b/17. This is the scalar alone, not a full prepared detector tuple.
2. [One common CM field](COMPACT-COMMON-CM-FIELD-FROM-THE-ACTUAL-SCALAR.md): the explicit t=21060 gives Q(√(1−t²δ)); it has the required 2/3/53 and old-support splitting, including every actual θ prime, before the remaining primes are chosen. It is an auxiliary field for the finite-detector route, not a substitute for a prescribed analytic h_*.
3. [Every compatible I row can be certified by one norm](ACTUAL-SCALAR-I-NORM-CERTIFICATE-EXISTENCE.md): narrow Hilbert class-field splitting, independently of the retained old CRT rows, supplies each of the seven I slots and a rational norm certificate for its entire θ incidence. This is an existence argument, not data for any specific prime.
4. [The exact test for a trial q₀](ACTUAL-Q0-IMAGINARY-CLASS-NUMBER-TEST.md): after the old rows have passed, the literal companion block is nonsingular precisely when the maximal-order imaginary class group of Q(√(−q₀δ)) has elementary abelian 2-primary part. This is the ordinary imaginary 4-rank, with **no** extra dyadic ray computation. The [old-block cancellation](ACTUAL-Q0-COMPANION-SCHUR.md) explains why this one companion block suffices. Given valid I, the arithmetic search in the retained prime ray terminates; no corresponding assertion about an added coefficient gate follows.

## Replay the exact bounded checks

All commands below use stock Python 3 and can run in this directory without repo tools:

```sh
sha256sum -c SHA256SUMS
python3 -B check_compact_field_parameter.py | diff -u EXACT-COMPACT-COMMON-FIELD-PARAMETER.json -
python3 -B check_q0_imaginary.py | diff -u Q0-IMAGINARY-CLASS-DIAGNOSTIC.json -
```

The first check replays the small t search and the explicitly certified local residues; it does not evaluate the large scalar from scratch. The second enumerates all reduced positive definite forms at the two small canaries (θ=145, q=7 and 43), independently of their signed and unsigned matrix checks. The canaries are not instances of the fixed production scalar. The optional residual-GL₂ observation in the I note uses the earlier [shorter odd source](../heegner-odd2544-shorter/INFINITE-MOD13-UNITS-BUT-NOT-SELECTED-SUPPORT.md); it is not required for either replay or for the I norm and q₀ gate.

The three main mathematical notes and both bounded replays were [cold-checked independently](INDEPENDENT-COMPACT-CM-I-Q0-REVIEW.md). No Lean theorem, numerical production I or q₀, or paired mod-13 nonvanishing is claimed. The actual maximal-order computation may require integer expansion or factoring internally. The improvement is a decision criterion without a factor list supplied to it, not a complexity bound.
