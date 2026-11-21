# An exact partial principal reduction of the actual ordinary mirror q53

Use the actual covector field F^c, integral generators B and Z and
[the isolated degree-13 prime at 53](../actual-one-I-ordinary-q53-ideal-r1/EXACT-ORDINARY-Q53-PRINCIPAL-CHART.md).
The fixed element gamma=Z−G(B), as defined there, has 53-part of
its divisor exactly that prime with exponent one. This packet computes
its entire signed norm and its small faithful support. It does not
claim a reduction to a small generating base or a class-rank bound.

## Cyclotomic-split relative norm

Write F_x=Q(u) for the degree-84 sign field of the original point,
u=x(P)/d, and U_a(u)=x([a]P)/d. Exact division polynomials give
U_a=u−ψ_(a−1)ψ_(a+1)/ψ_a², retaining the even-in-y numerator
in the untwisted normalized model. The y ratio is

    W([a]P)/W(P) = U_a′(u)/a,

by pulling back dx/(2y) under [a]. Hence for a given primitive
cyclotomic root z the Gaussian generator has expression

    Z = W Y_z(u),
    Y_z(u) = Σ_(a=1)^6 (z^a−z^(−a)) U_a′(u)/a.

The negative second term comes from the matched sign −[a]P;
there is no normalization factor. Since
F^c(ζ13)=F(ζ13) and both degree-168 fields are disjoint from the
cyclotomic field over Q, either base change computes the same
determinant for the rational norm of gamma. For primes splitting
13th roots of unity (ell≡1 mod13), specialize z to a literal
primitive root of order 13. The sign pair W,−W gives the exact
modular norm as a degree-84 quotient resultant of

    G(B)^2 − 13^4 d·u(u−1)(u+3) Y_z(u)^2.

Here B=half the sum of U_1,...,U_6. The replay works with
rational functions modulo the pinned monic x polynomial, with
unit denominators at each retained CRT prime. The earlier
exact bounds |v|<1456 and |B|<48 yield an integer archimedean
upper bound from |Z|≤12 max |W| and |G(B)|≤Σ|G_i|48^i.
The CRT product exceeds twice the bound, and a fresh split
prime verifies the signed result. No root-of-unity ambiguity
from taking a twelfth power of a full norm is used.

The exact norm has 2988 digits. Removing all rational prime
factors below 200000 gives

    |N(gamma)| = 3^31 · 17^6 · 53^13 · 5303 · C,

where the actual residual integer C has 2940 digits and remains
unfactored. Thus this purpose-selected principal relation is
not certified smooth enough for the small factor base.

## Exact projected small support

At 17 the actual central quadratic twist inertia is −I
and fixes every prime above it; the faithful ξ projection
is zero there. At 5303 the norm exponent one forces a single
degree-one mirror prime. Take the explicit quadratic residue
model in the replay. The relevant original point branch has
Frobenius −1 and ζ13 has Frobenius inversion, since
5303≡−1 mod13; these two signs match the diagonal invariance
of Z. The code reads the unique mirror zero, B=2787 and
Z=2508. This gives the actual q_5303 of norm 5303 with
valuation one in gamma. It is an address on the same F^c.

At 3 the exact Tate decomposition consists, on the mirror
side, of twelve degree-one formal covector primes in a free
relative orbit, and four other primes with nontrivial
stabilizer (these contribute zero in ξ). For the latter
description apply the contragredient action of matrices
(a,b;0,1), a in <3> of order three and b in F13, to the
nonzero covectors. The covectors with first coordinate zero
are fixed by the whole decomposition group; the other
covectors have decomposition orbit size 39 and relative
scalar stabilizer of order three.

Compute the free orbit in the unramified degree-three
Tate model through 3^4. The exact j=35152/9 gives Tate
parameter q_T ≡ 9/35152 modulo 81. The n=0 terms for a
nontrivial 13th root t are t/(1−t)^2, t²/(1−t)^3;
the other terms through this precision give corrections
q_T(t+t^−1−2) and q_T(1−t^−1), respectively. The minimal
change to x=U²X+R,y=U³(Y+X/2) is recovered from
U²=4(3R+2d) and
3R²+4dR−3d²=U^4·a4, with a4≡−5q_T mod81 and U≡1 mod3.
These exact equations give U=46,R=51 mod81.
Scaling ζ13 by a=1,…,12 yields the following exact
3-adic valuations on the free orbit:

    0,3,0,1,0,0,0,0,2,0,1,0.

All are strictly below the checked precision four.
With ξ(a)=a the coefficient on eξ[q_3] is their
a^−1-weighted sum, namely 4 modulo 13. The fixed
B and Z values modulo 81 and phase are archived.

Thus the genuine partial ordinary class relation is

    eξ[q_53] + 4 eξ[q_3] + eξ[q_5303]
           + eξ[positive divisor of gamma away from the displayed small primes]
      = 0.

The last term is an actual ideal of norm C, but no
smoothness or factorization at those primes is claimed.
This is a global principal row and a verified reduction
of the test class to two explicit small classes and a
remaining large component. It is not a basis or
saturation certificate, and no rank bound follows.

    sha256sum -c SHA256SUMS
    python3 -B check_q53_global_principal_norm.py | cmp - ACTUAL-Q53-GLOBAL-PRINCIPAL-NORM.json
    python3 -B check_q53_small_support.py | cmp - EXACT-Q53-SMALL-MIRROR-SUPPORT.json
