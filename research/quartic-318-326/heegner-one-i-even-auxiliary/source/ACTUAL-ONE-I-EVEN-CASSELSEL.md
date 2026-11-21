# An exact rank-zero even auxiliary on the literal one-I base

This computation fixes
`beta = 204618888056724185`, `p = 114649`, `q = 119851`, and
`d = beta*p*q = 2811626664334219040035976315`.
It does not change that selected base or compute its unknown marked rational point. Let
`E_e: y² = x(x−e)(x+3e)`. The explicit auxiliary here is

```
m = 7·13·19·283079 = 489443591,
D = m d = 1376132651143091791135781016804547165,
e = −D.
```

The four new primes are distinct and prime to `6·53·d`. The negative fundamental
discriminant `−m` splits every prime dividing `6d): at 2 and 3 use
`−m ≡ 1 mod 24`, and the exact verifies at the ten old odd primes are in the replay.
It is inert at 53, an additional fixed detector requirement. Thus this is a genuine
even auxiliary on that entire base bad support, not a small substitute d. It does not
certify split support for the still-unknown selected companion `dθ`.

## 1. Exact full 2-Selmer and rational tangent data

Use the literal Kummer order `(x, x+D, x−3D)`. The third squareclass is determined
by the first two; for a root replace the zero by the product of the two differences
to the other roots. Every global class in the Selmer group is supported on
`S = {∞,2,3} ∪ {p : p | D}`: away from it, odd good reduction gives the unramified
Kummer image. At each S-place, the witness rational x values in the JSON give a
local point (the prescribed cubic is a local square), or an actual rational
2-torsion point when x is a root. Their Kummer rows span by the exact dimensions:
1 at infinity, 3 at 2, and 2 at odd finite places. At an odd place use an open
pro-p subgroup of the elliptic point group, on which doubling is invertible;
in the finite quotient the number of elements killed by 2 equals the cokernel
size. At 2 an open torsion-free subgroup is isomorphic to an open additive copy
of Z₂, so the index is twice the cardinality of rational 2-torsion. At infinity
doubling surjects on the identity component and its component quotient has size 2.

The program computes each full local annihilator, restricts all its rows to the
global finite support, and obtains rank 30 in 34 binary coordinates. It separately
checks four independent kernel vectors: the actual Kummer classes of (0,0) and
(−D,0), and the representatives

```
λ = (a,1,a),   a = −53761071468515416235,
μ = (g,1,g),   g =      30496867310715.
```

In the first class put `x = a z1²/t²`, `x+D = z2²/t²`, `x−3D = a z3²/t²`.
This is the standard [Cassels full-2-torsion cover](https://doi.org/10.1515/crll.1998.001),
with ternary conics ordered by omitted coordinate. The exact primitive tangent
seed is

```
(A,B,C)=(13085423305160256669,91938296155961104467617803625,113276920682),
a A² + D C² = B².
```

Use `Q1=(2A,2B,C)` in coordinates `(z3,z2,t)` of conic 1, and
`Q3=(A,B,C)` in `(z1,z2,t)` of conic 3. The corresponding tangent linear
forms, dropping a rational prefactor, are

```
L1 = a A z3 − B z2 + 2D C t,
L3 = a A z1 − B z2 + D C t.
```

Conic 2 has a rational point `(z1,z3,t)=(1,1,0)`; its choice contributes nothing
because the middle coordinate of μ is 1. Indeed the [explicit Cassels tangent
formula, written in the cyclic omitted-coordinate convention](https://zhangshenxing.github.io/publications/WangZhang2022.pdf#page=5),
is the product of local symbols `(L1,g)_v (L3,g)_v`. That formula uses the
rational global tangent choices above; it is not a pairing of just local
squareclasses. Multiplying a fixed tangent form by a global nonzero rational
constant does not change the product by Hilbert reciprocity.

## 2. Genuine value and its consequence

At each retained place where g is not a local square, the certificate specifies
one rational x in the affine chart t=1 and three signed approximations to the roots
of `(x−e_i)/λ_i`, where `e_i=(0,−D,3D)`. The checker explicitly produces the
approximations by integer Hensel lifting, checks their error to the exact
rational target, and propagates Hensel precision through both tangent forms.
This determines their nonzero valuations and unit residues, and hence the
Hilbert symbols with no p-adic rounding. At infinity g is positive. A place
where g is a local square contributes +1 without needing a chosen point.

For an odd p outside `2·3·D`, both conics have good reduction and both global
tangent seeds are primitive. Normalize a local covering point to primitive
projective coordinates. Each of the two projections to its ternary conic
remains primitive: if the three coordinates vanished modulo p, an equation
with the fourth would give a nonzero unit times its square equal to zero.
If a tangent evaluation vanishes modulo p, the reduction is the marked conic
point, since a tangent line on a smooth conic meets it with multiplicity 2
there alone. Near that point the tangent cut has divisor twice the smooth
section; after a primitive projective coordinate is trivialized its value is
a unit times a squared local parameter. Thus its nonzero valuation is even.
Since g is a unit at p, both Hilbert symbols are +1. This justifies the
**complete** product without assuming integrality of arbitrary normalized x.

Exactly 2, 5 and 733 have product −1; hence the two Selmer classes pair to −1.
The Cassels pairing is the pullback of the alternating Cassels–Tate pairing
on Sha. Both classes therefore survive modulo the rational point image, and
the rank-four finite Selmer space has radical exactly the two known torsion
classes. The rational point image contains those two independent classes,
so rational rank is zero, and the order-2 part of Sha has dimension 2 with
nondegenerate pairing. Any element of order 4 would have a nonzero double
in this order-2 group orthogonal to all of it, because
`<2x,y>=<x,2y>=0` there. Therefore

```
rank E_{−D}(Q)=0,      Sha(E_{−D}/Q)[2∞]=(Z/2)².
```

There is no assumption of finite Sha in this argument. In particular the full
primary 2-Selmer group has corank zero. Applying [Burungale–Tian, Theorem A,
arXiv:2611.11566v1](https://arxiv.org/html/2611.11566v1#ThmtheoremA), the public
rank-zero 2-converse preprint, now gives `L(E_{−D},1) ≠ 0`. The authors state
that their proof does not invoke the OpenAI results. This is an application
of their rank-zero theorem only; the exact finite descent and rank-zero
arithmetic above do not depend on that preprint.

This certifies a genuine **nonzero central value**, not its analytic number,
primitive normalized 2-valuation, or mod-13 unit. It gives no derivative of
E_d, no corrected Heegner trace, no marked E_d point, and no assertion that the
same K is admissible for dθ or for another selected index.

## Reproduce

With ordinary Python 3 and no extra packages:

```sh
sha256sum -c SHA256SUMS
python3 -B check_even_auxiliary.py | cmp - EXACT-REPLAY.json
```

The rational tangent seed is a certificate input, not an oracle: direct
integer substitution and primitivity are checked. No approximate analytic
L-value, height search, or enumeration of Hilbert class orbits is needed.
