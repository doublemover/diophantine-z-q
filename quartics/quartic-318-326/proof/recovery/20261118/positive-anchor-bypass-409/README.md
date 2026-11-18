# Exact global bypass at one prepared pole, not merely local approximation

**For b=(204/1073)² the normalized rational PointPair has an explicit
solution with both ordinates nonzero, but the positive canonical anchor
has no rational point.** The same-place negative-anchor packet additionally
excludes the other possible torsion branch. Consequently *every* rational
PointPair at this particular b needs both ordinates nonzero. This is a
concrete separation between the original free-twist problem and both
one-ordinate-zero strategies. It is not a construction of the four poles
of a common original index, nor a blanket disproof of any rank statement.

## Same pole, same exact classes

Here β=17, θ=409, B=17b and V=B²(1−b/17). The primitive identity

    17·12²+409·53²=1073²

gives 1−b/17=409(53/1073)² globally, not just locally. This b is a
rational square, lies strictly between 0 and 17, has square reduced
denominator and depths (4,2,2) at 2,3,17. Apply the two-seed formulas
with λ=17/9, μ=81. They give s=−113/9,J=130/9,t=1085/27,K=1102/27;
the seed has h=9/89, b₀=(153/89)² and 1−b₀/17=409(4/89)². The
global transports X=356/3219 and Z=4717/4292 take the seed exactly to b.
For F_n(x)=x(x−n)(x+3n), the following rationals satisfy
y₁²=F_E(B), y₂²=F_(EV)(B S²):

    E  = 2014880256/4864365025
    S  = −1424848608/2768946245
    y₁ = −2495222615232/5219463671825
    y₂ = −115188947076336604087118173483290329088/
          4411321710125745115338446056112360723825.

These equations are checked both by direct substitution and by
reconstructing the two-seed transport. It matters that both the target
itself AND the global complementary squareclass are identical; real density
and finite-place approximation would establish neither.

## Positive anchor obstruction

Put N=6953. A point on the smooth projective positive canonical quartic

    W²=409(s²−17t²)(s²+51t²)

would give a point on E_N:y²=x(x−N)(x+3N) with x of squareclass 409:
for t≠0 put x=409(s/t)² and y=409(s/t)(W/t²). At t=0 a point
would require 409 square; at s=0 the radicand is negative. A zero
W cannot give a rational projective point as 17 is nonsquare and
−51 negative. Thus no exceptional endpoint evades the obstruction.

In root order (0,N,−3N) take descent coordinates ([x],[x−N]); at a
vanishing factor its usual value is the product of differences from
the other roots, and O has class (1,1). The full split two-descent is
a homomorphism from E(Q)/2E(Q) into the 2-Selmer group. Here the exact
local kernel contains 32 pairs; at first coordinate [409] the only two
are α=(409,1) and α+κ=(409,409), κ=(1,409). The local exactness and
absence of omitted primes are important. At odd good p all three x-root
valuations are even (negative valuations simultaneously even by the cubic,
and at most one positive for integral x). Thus global supports use only
−1,2,3,17,409. At each such good p the local image consists of all four
unit pairs: it is contained therein, and the local group modulo doubling
has size four. At ∞,2,3,17,409 that quotient has size 2,8,4,4,4
respectively, by the identity component at infinity and the formal-group
index formula with full rational 2-torsion at the finite places.
local_images.py exhausts the exact local groups by providing enough actual
local x (test the cubic's local squareness) and torsion images; verify.py
also rechecks the historical matrix conditions independently. This
likewise confirms ε=(−1,−2) is everywhere in the local Kummer images.

The difference κ is *globally* represented. For
x=(1218087481/14596605)² one has x−N=409(2384152/14596605)²
and x+3N=409(120390298/14596605)². Multiplying the three factors
gives a rational ordinate. It suffices, therefore, to obstruct α.

## Explicit nonzero Cassels row, no reliance on a rank computation

Apply the preexisting full two-Selmer tangent pairing formula in
PAIRING.md, exact digest below, to the prepared conic data
(β,θ,A,E₀,D)=(17,409,12,53,1073), ε=(x,y)=(−1,−2). Here E₀ is
the norm-equation numerator, not the free twist E in the witness.
Its hypotheses hold: β,θ coprime squarefree, β≡1 mod8,2 mod3,
θ≡1 mod8,1 mod3, primitive norm equation, and v₂(A)=2. The
formula specializes to the following products:

* At 2, let ℓ=2·1073·5, in local squareclass 10. The factors
  (ℓ,−1)₂ and (−ℓ,2)₂ are respectively +1 and −1. This follows
  directly from the dyadic Hilbert-symbol formula, using ℓ/2≡5 mod8.
* At 3 the factor is (−1)^v₃(−1)=+1. At 17 the two β-support
  exponents are v₁₇(−1),v₁₇(−2), both zero; likewise both exponents
  at 409 in the θ-support term are zero. Infinity contributes +1.
  At every other finite prime the evaluated primitive tangent factors
  have even valuations and unit second arguments after normalization,
  as in the full formula; denominator primes are not silently discarded.

For orientation, on the α-cover write V²=θ(s²−βt²),
U²=s²+3βt². The tangent forms indexed by ε's three entries
(−1,−2,2) are D U−E₀ V−2βA t, D(U−s), E₀ V−D s+βA t. On the
nonzero chart, after common projective normalization by 2/(U+s), the
second is 6βD times a square and can be dropped only *globally* by
Hilbert reciprocity; the two other forms retain that same normalization.
This is the convention used by the cited explicit row, not a formal
interpretation of a zero tangent at an endpoint. Its pairing convention
is the split-cubic Cassels formula [Shukla, §3.1.1, equations 3.1.3–4
and Theorem 3.3.7](https://epub.uni-bayreuth.de/id/eprint/8348/1/thesis.pdf).

Thus ⟨α,ε⟩=−1. Rational Kummer images lie in the radical, so α is not
represented, nor is α+κ since κ is represented. The positive canonical
quartic is genuinely empty over Q although its relevant full cover has
points at every completion. This reasoning does not assume finite Sha,
BSD or PARI correctness.

## Exactly why neither ordinate may vanish here

For a PointPair, B=βu² and V=θv² with uv≠0. If y₁=0, since B≠0 we
must have E=B or E=−B/3. In the positive case divide the second point's
coordinates by (uv)²,(uv)³ to get an E_N point of x-class β. Translation
by (N,0) multiplies the first descent coordinate by N, giving class θ,
which was just excluded. In the negative case EV=−3N(uv/3)². Dividing
by (uv/3)²,(uv/3)³ gives a point on E_(−3N) with x-class β. The separately
source-reviewed small negative-anchor packet, manifest
a7233aae406c3ec71591edfb90ece218a0f7c6fcca5504d2f72a4a620bacbd03,
rules this out by its own direct Cassels row: only (17,3) and
(17,1227) survive local tests in root order (0,9N,−3N); δ=(1,409)
pairs nontrivially with both, with sole negative local product at 2.
Its proof is separately backed up, not inferred from the positive row.
If y₂=0, the valid exact swap at fixed B,V sends

    (E,S,y₁,y₂) ↦ (EV/S², V/S, y₂/S³, y₁(V/S)³).

This reduces to the already excluded y₁=0 branches. None of the
scalings uses a zero denominator. These are consequences for actual
rational points, not assertions about analytic ranks.

For a redundant cross-check only, PARI 2.15.4 ellrank yields
[1,1,2,...] on E_N and [0,0,2,[]] on E_(−3N).
[PARI's ellrank documentation](https://pari.math.u-bordeaux.fr/dochtml/ref/Elliptic_curves.html#ellrank)
describes the unconditional upper bound. Neither proof above needs that
output. No Lean kernel audit or new instance of any designated original
integer-input pole is claimed.

Historical arithmetic dependencies: FULL-MATRIX.md SHA256
2d2a864bb8d48bde0c99f357c82586e8d64fe905bd08ffd42e19e556ce56dacd;
PAIRING.md SHA256
f4ca4fddc6afecd93539e71698908a840b9ea1d5ae412ae70160b30b035a7849.
Run python3 -B verify.py for the new positive certificate and
python3 -B local_images.py for the independent exhaustive local arithmetic.
