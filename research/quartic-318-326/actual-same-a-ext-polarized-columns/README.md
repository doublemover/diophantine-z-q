# Actual Ext classes and the polarized same-surface columns

For the literal D=210 chosen fine-model fibres above 13 and 5,
this comparison identifies the two actual directional cotangent
classes with the ordered polarized connecting columns of Yuan.
The rank is respectively two and one at the indicated smooth
height-one points, after evaluating a nonzero tangent. The
ramified determinant alone does not detect the nonzero column.
This is a classical proof with independent mathematical review,
not a Lean validation or a calculation of numerical entries of a
selected counterexample.

The exact proof discusses how to port two separate native lemmas;
their experimental sources, not kernel-checked, are not part of
this paper package. Neither the marked moduli problem nor the
represented Picard functor is claimed as a native theorem here.

## Exact replay

```sh
sha256sum -c SHA256SUMS
python3 replay_polarized_columns.py | cmp - EXACT-CLASS-AND-COLUMN-CONTROLS.json
```

The 196 matrix-frame controls, 2322 signed gauge triples, and 194
unit inverse/restriction checks are normalization canaries. The
ordered fibre ranges and branch conditions are proved separately
in the paper. The independent review binds the original exact
author seal `be38d86c2a5ffdf085972ca847bed49f97c96677ef6da38b2500b4950b5e0c00`.

## Earlier exact public arguments

- [ACTUAL-UNIVERSAL-FAMILY-AND-UNSCALED-KS.md](https://github.com/doublemover/diophantine-z-q/blob/10cc3d1f555c2a8faceb3af308990331096e8331/research/quartic-318-326/actual-same-a-yuan-period-metric/geometric-context/ACTUAL-UNIVERSAL-FAMILY-AND-UNSCALED-KS.md), SHA-256 `883f92a08419865a822720a38aa1e52069ecfd597e238f7d1c6fca7f72301b82`.
- [ACTUAL-YUAN-CECH-CONNECTING.md](https://github.com/doublemover/diophantine-z-q/blob/10cc3d1f555c2a8faceb3af308990331096e8331/research/quartic-318-326/actual-same-a-yuan-period-metric/geometric-context/ACTUAL-YUAN-CECH-CONNECTING.md), SHA-256 `1960f77c958561c3dcd52c68519a7ed78b461f1bbdaafa644655709d0c4f87de`.
- [SHARED-DT-SQUARE-ARITHMETIC-ANALYTIC-NORMALIZATION.md](https://github.com/doublemover/diophantine-z-q/blob/10cc3d1f555c2a8faceb3af308990331096e8331/research/quartic-318-326/actual-same-a-yuan-period-metric/shared-dt/SHARED-DT-SQUARE-ARITHMETIC-ANALYTIC-NORMALIZATION.md), SHA-256 `b9a4abd83c0158b2b39de6cc6d573946bc8632839a9417914ba390dc6271ec3d`.
- [ACTUAL-SAME-A-NONFLAT-KS-AND-THE-FINITE-PRIME-ROW.md](https://github.com/doublemover/diophantine-z-q/blob/10cc3d1f555c2a8faceb3af308990331096e8331/research/quartic-318-326/original-actual-same-a-ks-level-and-nonflat/ACTUAL-SAME-A-NONFLAT-KS-AND-THE-FINITE-PRIME-ROW.md), SHA-256 `b18fd4c88423f562238868f51bdfdd7e96c81ee1c1cf9e8597f8dd563a1f574d`.
