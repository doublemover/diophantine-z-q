# The original real norm margin holds in every nonempty even index progression

Let rho be the positive sqrt(2), K=Q(rho), d=3−rho and d'=3+rho.
Use the literal point R=(1+rho,2rho) on E_d:y²=x³−d²x and its
conjugate R'=(1−rho,−2rho) on E_d'. Put

    U_d(x,y)=2y/(x²+d²),    W(h)=U_d([h]R)·U_d'([h]R').

This is the exact real rational norm N_(K/Q)(U([h]R)) used for the
original chart. Let h₀ and L>0 be even integers. There are infinitely
many positive integers h=h₀+L n, n≥0, with h>1 and |W(h)|>1/100;
indeed either strict sign margin can be attained. This preserves
every fixed finite congruence already absorbed into this progression,
including any original mod-5 chart guard. It does not manufacture
such a progression when the elliptic order/depth constraints conflict.

## Exact non-torsion of the original source point

At p=313 both rho roots exist and d is a unit; the discriminant is
64d⁶, so both places of K have good reduction. The accompanying
small affine replay adds the literal R until its first return at
each place, giving the exact orders 6 and 17. Good reduction is
injective on prime-to-p torsion. For example, in the reduction
kernel the local parameter is in the maximal ideal and [m](z)
has unit linear coefficient m for p∤m, so a nonzero kernel element
cannot be killed by such an m. If R were torsion, the prime-to-313
part of its order would equal the prime-to-313 part of each
reduced order, which are distinct. Hence R is nontorsion, and
so is R' by conjugation.

## Exact independence in the two real arms

Both d,d'>0. Map them to the same curve E₀:Y²=X³−X by the exact
positive scalings

    P  = ((1+rho)/d,   2rho/(d sqrt(d))),
    P' = ((1−rho)/d', −2rho/(d' sqrt(d'))).

The inverses (x,y)=(dX,d sqrt(d)Y) and their conjugates are
pointed curve isomorphisms, so P,P' are nontorsion too.
The classes of d,d' are independent in K×/K×²: each has
norm 7, not a square in Q, and their product is 7, not a square
in K. To check the latter, a square (a+b rho)²=7 with a,b in Q
would have ab=0 and require the rational square 7 or 7/2.

Thus F=K(sqrt(d),sqrt(d')) is biquadratic over K. Its two independent
sign automorphisms respectively negate P but fix P', or negate P'
but fix P; the x coordinates are unchanged. If mP+nP' were torsion
for integers m,n, apply one automorphism and subtract to see that
2mP is torsion, which implies m=0. The other gives n=0.
This is independence modulo torsion on the same E₀, not just
separate non-torsion of the two original arms.

Let C=E₀(R)^0 be the real identity component, a circle group.
The cubic has three distinct real roots, so doubling sends both
points into C. Identify C as R/Z by its real Lie group law. If
the coordinates alpha,beta of 2P,2P' in this circle had a
nontrivial integral combination in Q/Z, the corresponding
point m·2P+n·2P' on E₀ would be torsion, already ruled out.
It follows that any nonzero integral character of C² is nontrivial
on every nonzero multiple of (2P,2P').

Now for h=h₀+Ln the pair ([h]P,[h]P') is a translate of
the nonnegative orbit of (L/2)·(2P,2P') in C². Each
nontrivial character averages to zero on that orbit by a
finite geometric sum with ratio not equal to 1. Trigonometric
polynomial approximation shows the orbit equidistributes for
Haar probability on C²; equivalently every nonempty open
subset receives infinitely many indices.

## Nonempty original acceptance open

In these positive scalings,

    U_d(x,y)=d^(-1/2)u₀(X,Y),    u₀(X,Y)=2Y/(X²+1).

Hence W(h)=u₀([h]P)u₀([h]P')/sqrt(7). The point (2,sqrt(6))
lies in the identity circle C; for instance the positive
branch X≥1 joins O through X→+∞. At the pair with both
coordinates equal to this point, the product divided by
sqrt(7) is 24/(25sqrt(7))>1/100. At the pair with opposite
ordinates it is strictly below −1/100. The same inequalities
hold in respective nonempty open neighborhoods of finite
points. Equidistribution in the exact progression therefore
proves the stated norm margin at infinitely many h>1.

This is a paper-level existence theorem, not an effective
bound on the first accepted h or an interval certificate for
a particular index. Once a compatible even progression is
known, enumerating it with refining exact interval arithmetic
can verify a passing index. It says nothing about producing
new compatible prime supports, square pole denominators,
a rational PointPair, or Lean.

Replay the literal non-torsion check with
    python3 -B check_nontorsion_313.py | cmp - EXACT-313-FIRST-ORDERS.json
    sha256sum -c SHA256SUMS
