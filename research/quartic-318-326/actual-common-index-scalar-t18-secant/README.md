# The common-index input-zero scalar: a relative class and a fixed secant test

This package records two independently reviewed reductions for **one fixed** choice of first rational point, `t=18`, at the original input-zero scalar. The [relative-class reduction](relative/COMMON-INDEX-SCALAR-T18-RELATIVE-ISOGENY-GATE.md) isolates the bare `x`-squareclass needed for the original raw companion; the [secant test](secant/FIXED-SECANT-TEST-FOR-THE-COMMON-SCALAR.md) gives an equivalent fixed-quartic criterion for that same companion. Neither paper computes the complement at an actual simultaneous four-pole index, determines the class, or gives a point or rank. The secant presentation does not give a second independent solvability test.

See the [independent review](cold/INDEPENDENT-COMMON-INDEX-SCALAR-T18-RELATIVE-SECANT-REVIEW.md). Run from this directory:

```sh
sha256sum -c SHA256SUMS
(cd relative && sha256sum -c SHA256SUMS)
(cd secant && sha256sum -c SHA256SUMS &&
  python3 -B replay_t18_fixed_secant.py | cmp - EXACT-T18-FIXED-SECANT.json)
(cd cold && sha256sum -c SHA256SUMS)
```
