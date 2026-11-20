# Exact finite isogeny descent after a literal scalar specialization

Scope: this is an effective finite test of the two **local** isogeny
Selmer groups once the actual scalar rational coefficient has been
instantiated. It does not test global rationality of the marked
torsor just by enumerating the local groups. No same-index h,c
have been numerically supplied to this descent.

Let c=C/Z>0 in lowest terms, H=Z²−βC²>0, K=9βH, M=8βC,
and L=M²−4K=4β(25βC²−9Z²)<0. These are the same integral
auxiliary curves from THETA-CLASS-ISOGENY-DESCENT.md:

    E  : y²=x(x² + (M²−2K)x + K²)
    E' : y²=x(x² + (4K−2M²)x + M²L) = x(x−M²)(x−L).

Their designated isogeny kernels are the respective (0,0) points.
Use the x-squareclass map on each curve, with x=0 special value
the constant coefficient K² or M²L, and O special value 1.
Thus the relevant connecting map for the x-class **on E** is
the one for the dual isogeny E'→E, not the isogeny E→E'.

## Local candidates and an actual finite test

The first set of candidates is positive signed squarefree d
supported on K; the second is any signed squarefree d' supported
on M²L. Outside the constant coefficient, even valuations follow
by dominance of x³ if v_p(x)<0 and of the constant-coefficient
times x if v_p(x)>0. On E negative x is excluded by its strictly
positive real quadratic factor (negative discriminant); on E'
both real signs are permitted (L<x<0 or x>M²).

The literal forms are

    w² = d  u⁴ + (M²−2K)u²v² + (K²/d) v⁴,
    w² = d' u⁴ + (4K−2M²)u²v² + (M²L/d') v⁴.

At u,v both nonzero, the substitutions to either appropriate
model are x=d(u/v)² and y=d·u·w/v³ (or use d'). If u=0,
the squareclass equals that of the constant coefficient and
the represented point is (0,0). If v=0, the squareclass is
1 and the represented point is O. This establishes the exact
local and global squareclass interpretation including boundaries.

Only p|2KML and the real place need local testing. At every
other p the binary quartic has four distinct geometric roots,
hence good genus-one reduction and an F_p point by Hasse,
which lifts. At each remaining finite p use the integral
primitive charts u=1 or v=1 and w∈Z_p. For each chart and m
compute the residues solving its equation modulo p^m.
An empty level excludes the chart. Conversely, compactness
of Z_p² guarantees an empty level whenever the chart has
no Q_p point. A nonempty result at one level
alone does not certify a lift. For the positive decision,
in parallel search residues with a strong Hensel inequality
in w or in the other free coordinate, v_p(F)>2v_p(∂F).
An actual Q_p point is smooth in its displayed chart because
the binary quartic is squarefree in characteristic zero; at
w=0 use the derivative in the other coordinate. Sufficiently
accurate approximations then meet the Hensel inequality.
So finite positive/negative certificates exist for each
candidate even at 2 or at a nonsplit multiplicative prime.

These local memberships are group conditions on the
squareclass vectors. They can be intersected linearly after
tabulating the local image subspace; no global search over x
or evaluation at unrelated scalar indices is needed.

## Efficient source-vs-dual residue pruning

At every odd p|H, p∤β,C,Z because c is in lowest terms and
integral at every p|β. For a=0 all these primes are ≥7
(5|β, and the prepared c is divisible by 2 and 3 locally).
Thus p∤M²L, and a dual candidate d' is a unit there. The
second quartic reduces to
d'·(u²−(M²/d') v²)² modulo p. If d' is a nonsquare then
M²/d' is a nonsquare too, so that binomial cannot vanish
on a primitive pair, and its nonzero product is a nonsquare.
If d' is a square unit the v=0 chart lifts immediately.
**Every dual Selmer candidate must therefore be a square at all
odd H primes.** In particular θ itself is not even a dual
class of allowed prime support when θ>1. This is not a
contradiction for θ on E: E is the class sought, and the
previous all-place calculation gives θ locally on E.

Further exact pruning at sufficiently odd primes, to be used
before a generic residue lift:

* If p≥7 divides C but p∤β (thus Z,H,L units), the first
  quartic reduces to d·(u²−(K/d)v²)². A square d works
  at v=0; a nonsquare d works precisely when K/d is a
  square unit, with exact witness u²=(K/d)v² and w=Muv.
  Since K has class β mod p, at split p (β square) only
  square d is admitted on E; at nonsplit p both unit classes
  are admitted.
* At the same p on E', v_p(M²L)=2v_p(C) is even and
  a'=4K−2M² is a unit of class β. A dual candidate
  divisible by p (once) can lift if β is square (use unit
  u,v, so the middle term is a square unit). If β is
  nonsquare no such d' lifts: with u,v units the middle
  term gives the nonsquare; with v nonunit the first
  term has unique odd valuation one; with u nonunit
  the middle and last valuations have opposite parity
  and the first is strictly larger than the middle, so
  the leading term is either odd or has nonsquare unit.
  The unit-class decisions can be left to the exact local
  test above without assuming a split model.
* If p≥7 divides 25βC²−9Z² and is prime to β,C,Z,
  then β is a square mod p and K is a square unit mod p.
  The first quartic is d·(u²+(K/d)v²)²+L u²v².
  A nonsquare d can only lift near a unit root of
  u²=−K/d in the chart v=1, so p≡3 mod4 is necessary.
  There the exact coordinate r=u+(K/d)/u is locally
  invertible (derivative 2 at the root), with r∈pZ_p,
  and the equation divided by u² is (w/u)²=d r²+L.
  If v_p(L) is odd, a unique leading term is either
  an odd-valued L or an even-valued nonsquare d r²,
  so no lift. If v_p(L)=2j is even, solve the unit norm
  equation z²−d r₀²=L/p^(2j) over F_p and lift; it has
  a smooth solution by surjectivity of the norm on the
  quadratic finite field. Then r=p^j r₀ recovers u by
  the local invertibility just proved. Thus a nonsquare
  unit on E lifts here iff p≡3 mod4 and v_p(L) is even.
  Retain the general local test for dual candidates.

## What the finite bound would (and would not) say

For θ>1, at least {1,β,θ,βθ} survive local tests on E:
βθ comes from the actual order-four point and the two
remaining nontrivial classes from the all-place cut by
adding that point. On E' the actual torsion at minimum
gives {1,L}, with class L nonidentity because L<0.
The rank identity for the two actual rational x-class
images is
    2^(rank E+2) = #α(E(Q)) · #α'(E'(Q)).
It follows from the two isogenies composing to [2], with
only one rational nonzero 2-torsion point on E and no
intersection of φ(E(Q)) with the nonzero kernel of the
dual. (If φ(P) is in that kernel, then [2]P=0.)

Consequently, if the specialized finite test returns the
minimal possible sizes 4 and 2, it proves rank ≤1. Then
rank 1 holds exactly when θ is globally represented on E;
rank 0 would make the two locally soluble non-torsion
classes fail global realization. A locally soluble class
and the upper bound do not alone decide which alternative
holds. Nor may a class on the dual be substituted for
the required class on E.

On the actual finite curve no rational 8-torsion is possible:
a hypothetical order-8 point would double to ±P (the two
halves of T, since E(Q)[2]={O,T}), but [2] has trivial
x-class and α(P)=βθ is nonsquare. Odd-primary torsion maps
trivially to the exponent-two x-class group. Hence a global
point of class θ or β for θ>1 would be nontorsion, not a
second exotic torsion branch.

If c is fixed and actual ranks/global obstructions become
available, the recovered parameter from a class-β point
must still be tested against the real and selected local
open sets before reading the two original rational marks.
A generic no-section result cannot forbid rank jumping
on this arithmetic fibre. Replacing the huge actual
scalar c by any convenient local-compatible rational is
not a specialization of the same proof data.
