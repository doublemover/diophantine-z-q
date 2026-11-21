# A rational surplus-root norm preserving the actual nineteen linked cells

Keep the exact original J, the accepted repaired numerical h, the
sixteen inherited w mod-p² cells and all three added repaired cells.
Write \(W=c_1w\) on the original middle detector chart, and
\(r_1(W)=W^2+1/2,\ r_2(W)=W^2+1\). The earlier genuine two-factor
rational W failed because \(r_1\) had inert odd-depth factors even
though the two other middle factors had exact controlled squareclass.
The present construction eliminates **all inert odd support** of
these two surplus factors, while retaining those nineteen cells.
It does not retain the complete fixed global squareclasses of
\(W^2+32/407\) and \(W^2-1/2399\).

## Explicit rational producer

For a nonzero rational \(u\) define
\[
 K(u)=u^4/2+3u^2/4+1/32.
\]
For any nonzero rational \(A\) put
\[
 W=\frac{A-K/A}{2u},\quad S=\frac{A+K/A}{2},\quad
 R=W^2+3/4+u^2.
\]
The direct identities are
\[
 S^2-u^2W^2=K,\qquad
 R^2-2S^2=(W^2+1/2)(W^2+1).
\]
They follow by subtraction of squares; no norm finiteness or
weak-approximation theorem on an elliptic curve is invoked.

Take \(u\) to be the product of the actual nineteen split primes
of the repaired exact packet. For the prescribed normalized
\(W_p\bmod p^2\), \(S_p^2=K+u^2 W_p^2\) has a unit root modulo
\(p^3\), since \(K\equiv1/32\) is a square unit at each of these
split primes and \(u\equiv0\bmod p\). Put
\(A_p=S_p+uW_p\bmod p^3\).
Then \(A_p\) is a unit and the numerator of W is
\(2uW_p\bmod p^3\). Because \(v_p(u)=1\), the resulting rational
variable \(W\) has the exact old \(W_p\bmod p^2\).
The divisor c₁ is a unit at these cells, so the old w cells are
literally unchanged.

At the desired small primes all \(u\) are units. If \(p\) is odd
and \(v_p(A)=-m<0\), \(K\) is integral and
\(v_p(K/A)>v_p(A)\), so \(v_p(W)=-m\).
At \(2\) the actual \(v_2(K)=-5\) (the three depths are
\(-1,-2,-5\)); choose \(v_2(A)=1-600\), so again A dominates
K/A and \(v_2(W)=-600\).
A single direct rational CRT chooses \(A\) with these negative
valuations at \(2,3,5,7,11,13,17,19,23,37,2399\)
and the prescribed \(A_p\bmod p^3\) at the nineteen cells.
Its numerator can be raised by the exact common CRT modulus
so that \(A>K+4u+1\), giving \(W>2\). The archived rational
\(W,R,S\) are checked by exact arithmetic; reduced W numerator
and denominator lengths are 4876 and 3444 bits. In particular
its exact \((v_2 W,v_3 W,v_{17} W)=(-600,-8,-1)\), so the
previous literal fold/trace proof at the same h applies
without changing the three mandatory small-place pole squares.
This is not a proof of the original real w-threshold after
division by c₁.

## Exact scope of the norm improvement

At any odd inert prime in \(\mathbb Q(\sqrt2)\), the norm
valuation is even. For \(v_p(W)<0\) each factor has even
valuation already. Otherwise both are integral and cannot
both be nonunits since their difference is \(1/2\).
Thus the norm identity suppresses all odd inert depths
individually in \(r_1,r_2\), not merely their aggregate.
Conversely, for a nonzero rational value of their product,
if every odd inert depth is even, then it is a norm:
\(\mathbb Z[\sqrt2]\) is norm-Euclidean and every split prime
has a generator of norm \(\pm p\); \(N(1+\sqrt2)=-1\),
\(N(\sqrt2)=-2\), and an inert \(p^2\) is \(N(p)\).
Multiplying these generators and their inverses realizes
the rational factorization. This equivalence concerns the
two surplus factors, not the other two root factors, split
orientations of any factor, or other literal scales.

Forcing either surplus factor to be a rational square
would imply that the other is a norm, but would violate
the actual inherited cells. Indeed if \(W^2+1=Z^2\) then
\(W^2+1/2=N(Z+\sqrt2/2)\); if \(W^2+1/2=Z^2\) then
\(W^2+1= -N(W+Z\sqrt2)\), again a norm.
At the genuine middle cell p=3641809 the former square
would have odd valuation one. At p=4247281 the latter has
the nonsquare unit residue 3194323. These two finite
obstructions are independent of making both factors
squares, which would also force a three-square arithmetic
progression of common difference \(1/2\), the classical
noncongruent squareclass 2.

## Why the original fixed positive pair needs a separate step

Write \(b=8912209\cdot1185793321,\ t=1/2399\).
On its rational conic \(C_b: W^2-bY^2=t\),
no generic norm identity for the product exists in
\(\mathbb Q(C_b)\). At a zero \(W^2=-c\), for
\(c=1/2,1\), the closed residue field is
\[
 \mathbb Q(\sqrt{-c},\sqrt{(-c-t)/b}).
\]
It is biquadratic: the 8912209-valuation in the second
squareclass is odd, and in the first is zero.
It does not contain \(\sqrt2\): the separate quadratic
classes are negative and their positive product
\(c(c+t)/b\) has odd 8912209-valuation. These zeroes are
simple and distinct on \(C_b\) because neither is \(t\)
or infinity. Thus they are inert horizontal places for
constant extension by \(\sqrt2\), and their odd
valuation excludes a generic norm. This is a function
field obstruction, not a prohibition on special rational
W over the fixed b conic.

If one chooses and fixes a single u in the explicit
producer, retaining b becomes one exact genus-one
problem:
\[
 C_{b,u}:\quad W^2-t=bY^2,\qquad W^2-e=Z^2,\qquad
 e=-K(u)/u^2<0,\qquad S=uZ.
\]
The four geometric branch values in W are distinct,
so this joint double cover has genus one. On
\(E_{b,u}:y^2=x(x-bt)(x-be)\), its
literal Kummer tuple is \((b,1,b)\), by
\[
 x=bW^2,\qquad y=b^2W Y Z .
\]
At infinity a point would require \(b\) square, so
this is not the trivial rational-boundary case.
Conversely a non-torsion point in that marked Kummer
coset, witnessed by the three rational square roots
of \((x/b,x-bt,(x-be)/b)\), gives the exact affine
equations and consequently the surplus norm.
Its localization to the old nineteen cells remains
an extra condition.

An equivalent simple quartic for a specialized u follows
using \(\lambda=-e=K/u^2\), \(D'=Z+W\), nonzero:
\[
 b\,V^2=(D'^2-\lambda)^2-4tD'^2,\quad
 V=2D'Y,\quad
 W=(D'-\lambda/D')/2.
\]
The rank or marked affine point plus localization on
this specified model is a genuine next arithmetic
test, not an automatic consequence of the rational
conic parameterization. If one also uses an analogous
producer for the product of the **other** two roots
without fixing b, the two split equations share
a rational boundary at infinity. That different
genus-one system has a rational identity; an affine
point in the nineteenth-cell opens still requires
actual MW control. Neither geometry makes all the
remaining prime-order conditions automatic.

Replay:

    python3 build_actual_middle_surplus_norm.py | cmp - EXACT-MIDDLE-SURPLUS-NORM.json

No new prime search, no Lean run and no PointPair claim.
