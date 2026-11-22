# A cubic norm test and its oriented ideal input

These are two separate checked steps for the literal level-48 receiver at protected inert 29.

1. The fixed Tate pairing detects whether the exact signed phase has order nine rather than order dividing three. It expresses that test as a cubic residue of the ratio of the two genuine CM half-norms, with one fixed rational shift working at all 224 supersingular flags.
2. The required cubic class is already determined by a single oriented norm-one fractional ideal in the actual odd imaginary twist field. A binary norm lattice recovers the relevant value up to a harmless sign. Neither an absolute norm nor an unoriented factorization is enough.

The fixed conductor-241 replay calibrates the cubic value only. This package does not compute a moving CM ideal, prove an actual original primitive phase nonzero, or infer any required global mark. A cube is inconclusive about a possible order-three phase.

Run the packaged exact replay from this directory:

```sh
sha256sum -c SHA256SUMS
(cd proof/ct-level48-fixed103-inert29-tate-cubic-r1 && python3 check_inert29_tate_cubic.py | cmp - EXACT-INERT29-TATE-CUBIC.json)
(cd proof/ct-level48-fixed103-inert29-imaginary-ideal-r2 && python3 check_inert29_imaginary_ideal.py | cmp - EXACT-INERT29-IMAGINARY-IDEAL.json)
```
