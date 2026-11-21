# Exact p=13 certificate targets on the original one-I curve

Two separate approaches are pinned on the **same fixed base**
`d=2811626664334219040035976315`, with original q=119851.

1. The [point-field reduction](actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13-CERTIFICATE-TARGET.md)
   proves the actual local conditions, including wild ordinary inertia at 13,
   the two local point-field degrees, and the signed global eigenspace
   of a concrete degree-168 field. Its unit dimension is seven and
   its sufficient local matrix has 14 rows.
2. The [cyclotomic test](actual-one-I-cyclotomic13-r1/FIXED-LEVEL-CYCLOTOMIC13-TEST.md)
   gives an exact finite expression for the first mod-13 coefficient
   using the actual level-48 odd Manin eigensymbol. Several positive
   and null finite controls are checked, not substituted for the
   original d.

**Open:** the actual class-group eigenspace rank, a certified global
basis and its local matrix, and the actual cyclotomic coefficient.
Neither approach here proves analytic or rational rank, finds a
rational point, or assumes finiteness of Tate–Shafarevich groups.
See the [independent review](independent-review/INDEPENDENT-P13-REVIEW.md).

## Replay

Run from this directory with Python 3 and SymPy 1.14.

```sh
sha256sum -c SHA256SUMS
for d in actual-* independent-review; do (cd "$d" && sha256sum -c SHA256SUMS); done
(
  cd actual-one-I-cyclotomic13-r1
  python3 -B check_local13_torsion.py | cmp - EXACT-LOCAL13-ORDINARY-WILD.json
  python3 -B check_point_field13_presentation.py | cmp - EXACT-POINT-FIELD-13.json
  python3 -B check_cyclotomic13.py | cmp - EXACT-CYCLOTOMIC-CONTROLS.json
)
(
  cd actual-one-I-galois-no-seed-transport-r1
  python3 -B check_residual_transvections.py | cmp - EXACT-MOD13-ELEMENTARY-CONTROLS.json
)
(
  cd actual-one-I-odd-descent-target-r1
  python3 -B check_odd_fields.py | cmp - EXACT-ODD-FIELD-CONTROLS.txt
)
(
  cd independent-review
  python3 -B check_local_orbits.py | cmp - EXACT-INDEPENDENT-LOCAL-ORBITS.json
)
```

No large class-group computation, remote arithmetic oracle, or Lean
build is run by this package.
