# One-scalar prefilter for actual fixed-b marked torsors

This is a necessary test for the exact fixed-b auxiliary chart and the
same nineteen old W balls. It does not prove a retained original
318/326 pole. It replaces the prior four-cover/two-coordinate check
when one scalar suffices to reject a candidate. It does not perform
Selmer 4, Selmer 8, rank, or classical Cassels–Tate computation.

Keep b=10568037907556089, t=1/2399, u positive integral odd, prime to
3 and 17. For λ=(16u⁴+24u²+1)/(32u²), let

    C : W²−t=bY², Z²−W²=λ,
    E : y²=x(x−bt)(x+bλ), x=bW², y=b²WYZ.

Take homogeneous coordinates (Z₀,Z₁,Z₂,H)=(W,bY,Z,1). The two conics
obtained by omitting coordinates 0 and 2, respectively, are

    Q₀ : Z₁²−b Z₂²+b(λ+t)H²=0,
    Q₂ : b Z₀²−Z₁²−bt H²=0.

Use the exact fixed rational seed on Q₂; solve just this one
rational ternary quadratic Q₀ for a primitive rational seed.
The script validates each conic identity. Let L₀,L₂ be their
rational homogeneous tangent forms with fixed primitive integer
conic normalization. No Q₁ tangent, fourth covering, or second
Selmer coordinate is needed.

## Mathematical rejection criterion

As in the independent u=258049 one-bit proof, let g=L₀L₂/H².
Its even divisor has half representing T₁=(bt,0) on the actual
Jacobian E: the deck transform of the two omitted-coordinate
involutions is precisely T₁. The global quadratic étale cover
defined by the normalized square root of g has a fiber class
g(P)∈Q×/(Q×)² at *every* rational P, including its tangent zeros
and poles. Away from zeros this is the literal evaluation. At
zeros/poles, division by an even power of a rational parameter
gives the same class; use étale fiber interpretation if needed.

For each finite place p included in the calculation choose a
certified C(Q_p) reference P_p with g(P_p) nonzero. On
C(Q_p)=P_p+E(Q_p), g changes by the literal Kummer coordinate
x−bt up to squares. This follows by comparing the half divisor
to [T₁]−[O] over Q_p and taking the ratio as a constant times a
square; evaluating near O identifies the constant with g(P_p).
Thus allowable local values form the affine set

    g(P_p) · { δ_{T₁}(R) : R∈E(Q_p) },

with exceptional torsion values in the local connecting map.
The solver projects to the scalar only *after* it has reached
the exact full local tuple count: four at odd p and eight at 2.
Indeed on a sufficiently small formal open subgroup of E(Q_p),
[2] is bijective at odd p and has index 2 at p=2. Its kernel on
E(Q_p) is the four named rational 2-torsion points, giving the
cardinalities by the finite quotient index formula. Actual
affine x rows are accepted only when the product of all three
descent coordinates is square; Hensel then gives real local
points on the p-adic curve. At a place where the bounded
witness search does not reach this full count, no constraint is
deduced. Same for unavailable finite precision in g(P_p).

Every prime outside the explicitly reconstructed support
2·b·2399·u·num(λ)·num(λ+t) is good with diagonal form
coefficients and all root differences units. Both conic
projections extend on the smooth model, the primitive seeds
reduce to smooth conic sections, and their tangent sections
remain exactly twice those sections. Thus the quadratic cover
extends étale over each of these local models: its fibers at
integral proper points are unramified quadratic classes, even
if the point hits a tangent. The global class is therefore in
the signed squarefree span of precisely the displayed finite
prime support. This is an exhaustive necessary support
argument, not an a priori bound on coordinates.

Encode the affine local sets by binary annihilating linear
forms on that global support. A row combination (left 0,
right 1) excludes **every rational point on C**, even before a
particular contact condition. If consistent, at an actual good
contact take the two local root signs of Y and Z at the given
W mod p² center. Only use the ball if both radicands and their
roots are units and every needed tangent leading coefficient is
certified stable under the entire p² ball. If all four sign
branches require the opposite of a scalar Legendre bit forced
by the affine rows, then this one ball excludes a rational
marked point. The output includes the exact row combination as
an integer bitmask. Unforced, singular or insufficiently
resolved cells may be skipped, never turned into rejections.

The free prior first stage rejects any known non-square unit
root mod p on the actual W cell: no conic solve needed. Large
prime factors supplied by the input are checked by recursive
Pocklington certificates above 64 bits and the pinned
deterministic SymPy primality path below; all factorizations
multiply back to the literal coefficients. Failure to factor,
prove primality, or find a tangent is `unknown`, never a
mathematical obstruction.

## Frozen bounded results on Joined's 17 prior local-pass inputs

The input is the 17 factorized local-pass rows of the pre-existing
Joined wheel/support calculation up to 8,000,000. The script
rechecks their literal λ, λ+t, and factorization. It does not
search that interval or make a completeness statement about
other parameterizations or other u's. For these 17 no needed
local row or factor proof was skipped.

| Disposition | u (and individual mismatch place where relevant) |
|---|---|
| No rational point on this C: global affine scalar contradiction | 2862527, 5717647, 7264991, 7316873 |
| Cannot meet the named one original W cell | 258049 (52056721), 4823065 (583021393), 5349487 (575921), 6152345 (52056721), 7347941 (344853841), 7417949 (4818481), 7532197 (344853841) |
| Not excluded by this necessary scalar test | 2749849, 2891117, 3262241, 5685821, 5791843, 6162461 |

The six survivors have **no established rational point, sufficient
contact local-global criterion, or rank**. Pursue the independent
g₀ projection or the two-coordinate affine compatibility just on
those survivors before any higher descent. If either branch later
finds a literal point, use the original frozen contacts rather than
a supplied unmarked point on E. These packets do not supply either
original same-pole twist parameter or a universal existence theorem.

Run both replays from this directory:

    python -B cheap_fixed_b_tangent_scalar_gate.py 258049 1 5 11 2399 2891117 3262241 5717647 5791843 6152345 | cmp - EXACT-SCALAR-GATE-CONTROLS.json
    args=$(jq -r '.[][0]' JOINED-LOCAL-PASS-INPUTS.json | paste -s -d' ')
    python -B cheap_fixed_b_tangent_scalar_gate.py $args | cmp - EXACT-SCALAR-GATE-JOINED-CANDIDATES.json

No Lean run, remote writes, or user-computer action.
