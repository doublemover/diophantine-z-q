# Actual affine relative differential sheaves and frames

Two modules, seven public theorems, ten explicit object/map definitions and one
global-sections abbreviation pass strict kernel checking. The exhaustive
recursive audit covers 23 declarations with standard axioms only.

`AffineDifferentialSheaf318.differentialSheaf` is a genuine Mathlib
`Scheme.Modules` object on Spec(S): the actual tilde sheaf of Ω(S/R). It is not
a separate record mimicking a sheaf. An actual Kähler frame gives an actual
O-module sheaf isomorphism to the structure sheaf through the tilde functor.
Actual global universal-differential sections are constructed using the
canonical tilde/global-sections isomorphism. Their normalized frame values and
unique global frame coefficients are proved. A categorical naturality theorem
binds the sheaf frame map to this same global-sections frame, explicitly
retaining the canonical tilde(S)-to-O isomorphism; the two maps are not merely
asserted to match.

`WeierstrassDifferentialSheaf318` constructs these genuine sheaves and frame
isomorphisms on both actual finite Jacobian chart schemes and the actual
infinity Jacobian chart. The dx or dy universal differential gives the
normalized genuine global section on the appropriate chart. The literal
integral OpenJ family receives these exact sheaf objects, not an assumed
trivialization or a chosen replacement line.

## Exact boundary

These are relative differential sheaves of the elliptic family over its
stated base. They have not been glued here across all actual Weierstrass
chart overlaps, identified with a global relative dualizing/Hodge object, or
identified with the cotangent or bicanonical line of a compact modular/PEL
base curve. Subsequent gluing must use actual overlap differential transport.
No global arithmetic/analytic realization, section metric identification, or
GeometricRealization is claimed.

Replay `bash verify.sh`. Lean 4.35.0, pinned Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, debug.skipKernelTC=false.
The official Mathlib cache supplied 81 missing dependencies for the actual
tilde-sheaf API; no Mathlib source, frozen producer, repository or Git file was
modified. Generated compiler files are not deliverables.
