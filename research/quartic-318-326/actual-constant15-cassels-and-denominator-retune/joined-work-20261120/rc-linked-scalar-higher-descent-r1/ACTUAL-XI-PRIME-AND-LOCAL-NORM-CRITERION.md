# Two actual new ξ primes and the remaining local norm criterion

Fixed h=473592745039516333133760 and the same J, b, β as the
materialized a=0 scalar. Let c=C/Z>0 in lowest terms, D=βc²,
δ=1−D, H=Z²−βC², and L=25βC²−9Z². The first higher lift uses
homogeneous forms G=βd²−a² and
F=(9Z²−βC²)G+48βCZad−80β²C²d².
For the signed rational class ξ, write the lift as
`G=ξ V², F=ξ U²`. This note determines the LOCAL solubility
criterion on eight explicit second-stage classes; it does not supply
rational points on any of their global covering curves.

## Literal modular values

The companion checker reduces the exact literal elliptic-chart circuit W
at accessible primes up to 85,000, never replacing it by the W=1
surrogate. At p∤17R(1+A) where chart evaluations are accessible, the
nonconstant support conditions are c≡0 for C, and 25βc²≡9 for L.
For any new odd p|ξ β must be a square (apart from the already fixed
β ramified primes), so the scan uses this necessary filter. It skips
430 inaccessible places, not treating them as excluded.

Two simple L factors are certified, both eligible at their own place:
    p=2027:   25D−9 ≡ 217·2027     (mod 2027²),
    p=83761:  25D−9 ≡ 57074·83761  (mod 83761²).
The first modular lift uses the inert quadratic basis at p=2027;
the second uses both split completions at p=83761. All chart
denominators and needed nonzero mantissas are checked at extraction.
At either p v_p(c)≥0 (in fact c is a unit), hence Z is a unit.
Thus v_p L=1 in the actual reduced numerator, not just in a
temporary unreduced formula.

The omitted source-model bad prime 7 is resolved separately. The two
split residues are sqrt(2)=3,4. At the first component D_curve=0 and R
reduces to the smooth cusp-group locus; direct repeated addition gives
order 7 without a Hasse assumption. At the other component it gives
4. The former model is minimal at that component (valuation of
discriminant 6), and usual smooth reduction and the formal group
justify reduction modulo 7 times the first-return orders for 7².
The two chart values mod49 are (10,14) at h and (31,14) at s−1.
Their norms are both 42 mod49, so the quotient in W can be reduced
by cancelling the same single 7. This gives W≡5, c≡1 and D≡2 mod7;
thus none of β,C,H,L is divisible by 7 and the auxiliary lift is
good there.

## Exact local criterion at C and L (p≥11 outside fixed support)

Take a primitive pair (a,d) at p, and use the affine slope r=a/d
near any common root. If p divides G and ξ is ramified, d is a unit.
On the C branch, after lifting the two simple G roots over Q_p
when β is split, both F roots reduce to the two G roots. In each
pair the root separation has valuation v_p(C), because evaluating F
at the corresponding G root gives
`16βC(3Z r−5βC)` with its final factor unit. The quotient of root
cofactors for F/G reduces to 9Z² (square). If β is inert,
G is the negative of an unramified quadratic norm, hence ξ must
be a unit.

On the L branch β is split, and exactly one F root reduces to a
G root, specified by `3Z r_0=5βC mod p`. If r_1 is the nearby
F root, v_p(r_1−r_0)=v_p L: evaluate F at r_0 and multiply
`3Z r_0−5β C` by its plus-sign partner, which is a unit.
The quotient of cofactors reduces to −144 Z²/25. Put
e=v_p(r−r_0), f=v_p(r_1−r_0). For a ramified ξ we need e odd.
If e<f the quotient has unit class −1, and if e>f its valuation
is f−e. Thus p≡3 mod4 and f even prohibits ramified ξ at its
own place. If p≡1 mod4 and f>1, e=1<f works. If f is odd, set
e=f and tune the first unit coefficient x=(r−r_0)/p^f.
The two constraints prescribe independent Legendre signs of
x and x−t with t=(r_1−r_0)/p^f a unit. For either prescribed
signs their count on F_p\{0,t} is at least (p−5)/4, by the three
linear/quadratic character sums. Thus BOTH ramified ξ unit labels
are possible at a simple L prime; this applies exactly at 2027 and
83761. The same tuning handles v_p(C)=1 at a split C-branch,
and e=1<v_p(C) handles larger C depth.

For unit ξ, all unit classes are allowed at either branch.
At C the reduction F/G is the square unit 9Z² on the
open with G a unit, and quadratic norms in the residue field
give both unit classes. At L, pick r where all three distinct
residue roots are avoided. Prescribing χ(G)=χ(F)=χ(ξ)
gives at least (p−9)/4 choices: each of χG, χF, χ(GF) is a
quadratic character sum up to at most one removed nonzero term
after the cancellation of the common linear factor. This gives
both classes for p≥11. The p7 case did not require this count.

## All places other than the remaining H congruence

At every odd p|H, c,Z and β are units, β is a square unit,
and F reduces to `−8Z²(a−3βcd)²`, so the first lift requires
ξ to have unit class −2. Conversely choose d=1 and a away from
the double F root and the two G roots with χG=χ(−2):
the exact sum for χ(β−a²) shows it takes each unit class at
least (p−3)/2 times, and removing the F root loses at most
one. Here p≥7; there is no H at p7. This proves sufficiency.

At p|β, the two possible local classes of ξ are precisely
{−1,β}: they are attained with primitive pairs mod p near
(a,d)=(1,0),(0,1) respectively; F/G has square unit class
9Z² since c is integral and Z unit. At 3 we have v₃(c)=1.
Writing c=3c₁, c₁ a unit, one gets
    F/(9Z²) ≡ a²−c₁ad+2d² (mod 3),  G≡−a²−d² (mod 3).
The primitive pair (0,1) permits the nonsquare unit class;
unit a,d with ad≡−c₁ give the square class. No ramified class
can occur since β is inert, so the only criterion is v₃ξ even.

At 2, v₂(c)=2 and β≡1 mod8, and Z is a unit. When exactly
one of a,d is odd, all four odd residues of G modulo8 occur
and F/G has square unit class (the cross term has valuation
at least 6). When both are odd choose d=1 with G=8u, where
u is any odd unit: a²=β−8u is a square. The cross term
then affects F/G only at depth at least 3, so every ramified
unit label also occurs. Thus no additional dyadic restriction.
At the real place F,G are both positive at a=0,d=1 because
D<1/9, and both negative for large a/d, so both signs are
allowed.

At every other odd non-support place both forms have two
simple roots and their resultant is a unit. Their simultaneous
quadrics have good genus-one reduction, regardless of which
unit class ξ represents, and hence a smooth local point by
Hasse. The uniform proof also applies to p|Z away from
β,C,L,H; the cleared integral forms, not the local rational
c, are used for good reduction.

## Eight explicit candidates and one exact remaining criterion per candidate

On the group generated by −1,2,the eight β primes,2027,83761,
test only the local conditions at β support and the two known
H primes 131 and 6551. Exact enumeration yields no candidate
with neither new prime and none with both. It leaves four with
2027 and four with 83761, listed in the JSON. Every one of these
EIGHT candidates passes the other places **except possibly
additional primes dividing H** by the classifications above.
Here H>0, H is odd and coprime to every such ξ. For each of
these explicit ξ, the entire first-lift local-solubility question
therefore reduces exactly to the single congruence
    X² ≡ −2 ξ  (mod H).
Unit Hensel and CRT prove this equivalence, even if H has
repeated prime factors. A primitive norm representation of a
multiple of H for Q(√(−2ξ)) would suffice (and seeking one
with a coordinate 1 is exactly the modular problem).

The aggregate Jacobi symbol cannot resolve this residual:
H is a square unit at every odd prime dividing ξ (at C or β
use H≡Z²; at L use H≡16Z²/25); H≡1 mod8. Hence
(−2ξ/H)=1 automatically, even for a candidate that fails at
two unseen H primes. One must certify the actual square root
modulo H, an obstructing H prime, or an equivalent all-prime
primitive norm argument; the full H factorization is not
needed to STATE that precise input. Even a positive local
result for some ξ does not produce a global point on its
genus-one intersection. Unknown C/L factors can still give
other ξ choices; the scan is not a complete elimination.
