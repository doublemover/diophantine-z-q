# Original-parameter cotangent evaluation on the same signed center

Inactive source-only research draft. No local Lean/compiler run, hosted pass,
compiled axiom audit, maximal-model comparison, KS estimate, height theorem or
GeometricRealization is claimed.

## Construction

NormalizedReciprocalParameter318 constructs a K-algebra endomorphism of
TrivSqZeroExt K K by the native map of its second coordinate. It composes that
endomorphism with the existing whole reciprocal-order first-order point. The
scalar is explicitly -(t^-1)^2. Projection is exactly the same A→V→K point f.
The original parameter jet (t,1) times the constructed reciprocal coordinate
jet is 1 when t is nonzero, proving the normalization from the coordinate
identity rather than assuming a chain-rule label.

The native universal cotangent evaluator is then extracted from that new
first-order map. On every 1 tensor D(x), its value is the old Dw-normalized
value times -t^-2. All four normalized signed root derivatives are stated
explicitly, retaining d_i*(1-2*a_i/t)/(2*z_i). The quadratic identity on every
pair of differential generators has scalar t^-4. This statement is not a
claim about equality of integral lattices, every abstract tensor, or an
unconstructed global section.

OriginalParameterAllPlaceEvaluations318 uses the original signed square
relations and nonzero radicands, calls chart_center_alg exactly once, retains
its same u/e/s, coefficients, points f, polynomial evaluations, all four root
relations and finite/reciprocal alternatives, and appends the actual constructed
functional. Finite DT still evaluates to 1. Reciprocal Dw evaluates to -t^-2,
not 1. The reciprocal branch retains t≠0, so this value is nonzero by factor_ne.
No root sign, parity or center is reselected.

## Scope

V remains any DVR and K its characteristic-zero fraction field. Twists need
not be units in V; residue characteristic two is permitted. Two and nonzero
root values are inverted only in K by the inherited first-order construction.
The nonzero-radicand restriction is explicit: root-zero/branch points are not
covered by this derivative route. The original all-point center is unchanged.
The rescaling scalar is not asserted integral or an integral unit. Singular
orders and cotangent torsion are not ruled out by an unmentioned assumption.

## Missing geometry

This resolves only the first-order reciprocal coordinate scalar for the
constructed evaluator. The correspondence with the original rational
bicanonical frames and original global section lifts still requires proof.
No naive cotangent image is identified with a regular/maximal model's
dualizing-square lattice. The Hodge determinant, actual native KS map and
lower image, archimedean metric pullback, finite support, and height bounds
remain separate obligations. There is no per-point GeometricRealization yet.

## Provenance and verification

The root snapshot is the independently source-reviewed center-r70 successor
of published2428de0, not an assertion that center-r70 has compiled. The six
research prerequisites and two earlier adapters are the exact reviewed
current Library source bytes; their earlier research contracts and status are
retained. Native TrivSqZeroExt.map/fst_map/snd_map are read from the pinned
Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679 source. The future closure is
explicit and inactive. Only a fresh hosted run can establish Lean acceptance.
