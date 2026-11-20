# Independent checks: actual End orders at 53 and first lift of the fixed scalar

Exact review inputs:
* q=13 actual End manuscript d8c73eb613a19bd6866cfd7777ef3c7d8f3b2bece14ff72732f7f46a4c3f2697,
  script 5ec80a5cc9b8c2bf859bff1a1a906fa3f850dcf915ec3f95478103ae8a708c04,
  output 7f249c658e3d76cbba130204e9e3f2db02be45f9c78069f83cdac26bdfce8db4.
* q=29 prime-to-auxiliary rebase script 43da92f11cf856cdf3f764ae304a270fe1d4ed982c6c6f09bce135fd036af794,
  output aa650e289ef886c824cf93414845c9586c12e5db0d640f6a6d48452ca9bb1a8e.
* Fixed-scalar first lift manuscript ee7fd83fb1a7166da4c83fed597acf14a675333421bfa6986e2c32acda4524b4,
  script de5062709716812b69f402f69c79a75364db5b54500c951e5032cd74e4db5327,
  output d6d3c5e984f9f43ba5c34b8399c627c54881e0fec68e2f70e527e2ac4042acf0.

Both full finite End/mark calculations and the fixed-support calculation replay
byte-identically. The adjacent independent script takes a directory containing
the three named input JSONs and checks the exact cross-bindings plus independent
lattice congruences, norm-one rebases, squareclass masks, and conic identities.

## Actual orders, not abstract orders merely of the right discriminant

On the actual E0 the cube map over F53 gives trace(F)=0, and the explicit
automorphism gives Fω=barω F with J=1+2ω, J²=−3. Since J=ω−ω²,
the fixed points of ω are precisely its kernel of order 3 (degree 3 and
separable at 53). F fixes all three. The quotient property of the actual
separable J thus makes γ=(F−1)/J on the right integral. The rank-four
integral lattice (1,ω,γ,ωγ) is a superlattice of (1,ω,F,ωF) of index 3:
γ=J(1+F)/3 and F=−Jγ−1. The signed trace determinant has absolute
value 53² because the smaller lattice has absolute value (3·53)².
Ramification at 53 forces the lattice to equal geometric End(E0).

For an actual separable π of degree q, η=π⁻¹κπ is α/q with integral
α=π∨κπ. Conversely π α π∨ factors through [q²] iff it kills E'[q²].
The exact image of E'[q²] under π∨ equals {[q]X∈ker π}; the reverse
inclusion uses an arbitrary geometric preimage y and
[q²]y=π([q]X)=0. In a lifted basis adapted to ker π, the preimage is
<e1,q e2> and ker π=<q e1> mod q². The 11,22 entry divisibility mod q
and 21 entry vanishing mod q² are then exact. Both q bases give determinant
unit for the full coefficient-to-matrix map, so the checked lattice has
precisely index q⁴ before division by q and is the complete inverse image.

The map normalization can be checked algebraically, beyond sample signs:
for each pair ±Q with abscissa u and f(x)=x³+A x+B, the x-Vélu summand is
4f(x)/(x−u)²−2f'(x)/(x−u)+2(x−u). Summing yields exactly the
kernel-polynomial derivative formula in the checked source, including
the monic squared kernel denominator; y is obtained by differentiating
this x formula with normalized invariant differential one. This is why the
coordinate evaluations are the actual arrows. Integral 16- and 3-actions
recompute the literal transported cyclic subgroups and same 416 addresses;
no isomorphism inferred solely from shared j. The anti-Frobenius λ labels
agree exactly under q13 and q29 (32+4·96).

At q29, ω is irreducible mod 29, and any lift of the actual P generates
the unramified quadratic local module mod 29². F acts by u times conjugation
with N(u)=−53. All same-residue lifts of u with this norm are realized by
basis changes v=1+29s: the ratio is 1+29t, Tr(t)=0, and s=−t/2 gives
bar(v)/v=1+29t. The independent checker enumerates all 29 attainable
lifts as a control and verifies correct sign orientation. q29 is prime to
48 and the auxiliary 146965 (and to 455); it removes the q13 transport
issue, not the need to choose and justify actual type-I/II weights. For
each of the 416 marked orders, independent checks show both line-preserving
linear conditions hold and the index is precisely 16·3. Since q is a unit
at these levels, the global denominator does not change either line condition.
No modular lift, local L-value or coefficient/weight identity is certified.

## First higher lift on the same fixed h/J auxiliary chart

Completing the quadratic after replacing k² by X gives
βu²−v²=25D−9, with u=(18X+82D−18)/(16βc) and v=6H/(16βc).
Both rational points over u=5c have v=±3 and give
X=1−D/9≡8/9 at 131, a nonsquare. All potentially lifting points
therefore give a finite rational slope a/d. Substitution gives exactly
X=F/(9Z²G). The two binary forms have the stated negative norm
representations over the actual fixed Q(√β). At the two roots
a=±√β d of G the numerator values are
16βC(±3Z√β−5βC)d², giving resultant up to sign
(16βC)²β(25βC²−9Z²). Primitivity makes d a unit whenever p|G.
Thus every odd p in the common class ξ lies in this resultant; Z is
not a separate necessary factor.

Local at 131 and 6551, D≡1 and c,Z,β are units (β square). The actual F
reduces to −8Z²(a−3βcd)². If this is nonzero, its class is −2.
Otherwise d is a unit and G≡−8βd² gives the same class. At 131
it is square and at 6551 nonsquare. The other exact retained constraints
are even valuation at 3 (inert) and local class −1 or β at the eight
β-primes. Independent masks reproduce all 2048 signed squareclasses and
the 8→4→0 terminal progress. Thus every solution of this fixed cut, at
any height, needs a new odd prime in the signed squareclass ξ from
C(25βC²−9Z²). This does not prove that no auxiliary solution or original
PointPair exists; possible new support is not excluded. No Lean/build.
