# Geometric rank one and rational rank zero on the changed norm conic

Fix the same positive squarefree Ready classes β and θ from the changed
Möbius receiver, with β, θ and βθ all nonsquare. For the original
nontrivial-companion case this last condition is automatic from
gcd(β,θ)=1 and β,θ>1. The norm conic N: βc²+θe²=1 is smooth and has the
given rational norm point. Let K=Q(N); the notation Qbar(N) extends the
constant field, *not* to an algebraic closure of K. The result concerns
only the exact changed Möbius receiver, not the arbitrary two-parameter
marked surface or all rational specializations.

Put μ=βc², δ=1−μ=θe². The receiver and its Jacobian and signed quotient
remain exactly those of the predecessor:

    W² = H(t) [(1+βct)²−9β(t+c)²],      H(t)=1−9βt²,
    J:  Y²=X(X−16μ²)(X−μ(25μ−9)),
    J′: Y²=X[X²+2μ(41μ−9)X+(9μδ)²].

**Result.** J and J′ have geometric function-field rank one over
Qbar(N) and rational function-field rank zero over K. The exact
rational 2-primary torsion of J′ over K is the cyclic group of order
four already visible in the predecessor. Its positive scalar isogeny
Kummer classes are 1 and βθ, not β or θ. Moreover at **every rational
specialization on N** the same statement about the *positive torsion
x-classes* holds, even where rational 2-torsion grows. A rational
solution of the changed receiver at a specific c therefore forces a
genuine positive-rank specialization and the specified β Kummer
class; no rank or class at a specific original pole is asserted.

## 1. The total receiver is geometrically a Kummer surface

Let G(t)=1−βt². On the open where the denominators below are nonzero,
the function field of the total family is equivalently that of

    a²=θG(t)G(t′),       b²=H(t)H(t′).

The actual change of variables and its inverse use

    t′=(t+c)/(1+βct),
    c=(t′−t)/(1−βtt′),   e=a/[θ(1−βtt′)],
    W=b(1+βct).

The identity δ=G(t)G(t′)/(1−βtt′)² proves the conic relation;
the last equality is the literal receiver, not a substitution of
a different isogeny. Over Qbar the two independent square roots
a,b are the products of the respective roots on the two curves

    u²=G(t),          v²=H(t),
    u′²=θG(t′),      v′²=H(t′).

Each curve has genus one: the biquadratic map to the t-line has
four distinct simple finite branch points, each with inertia 2,
and is unramified at infinity. Each single sign flip has fixed
points and acts as −1 up to a translation on its elliptic curve.
The flip of both u and v has no fixed points, even at infinity,
and is translation by a nonzero 2-torsion point. These statements
also hold for the primed curve.

The diagonal four-element sign group on the product has exactly
the displayed function field of invariants: all four individual
squareclasses over the t,t′-plane are independent by their
separate simple branch divisors, and the two product radicals
generate a degree-four invariant extension. First quotient by
the diagonal simultaneous-both flip, a translation by a
2-torsion point of the product. This is an abelian surface B
isogenous to the two elliptic factors' product. The remaining
nontrivial diagonal sign flip descends to −1 up to a translation
of B, which over Qbar is conjugate by a translation to −1.
Thus the smooth minimal surface is the Kummer of B.

The two elliptic factors are geometrically isogenous to the
non-CM curve E₁ of the first mark: take the product uv, absorb the
constant β as a square over Qbar, and then use the nonconstant
first-mark map from D(t)^(1/2) to E₁. Its j-invariant is 35152/9,
not an algebraic integer, so it has no CM. An abelian surface
isogenous to the square of a non-CM elliptic curve has
Néron–Severi rank 3, since the rational symmetric endomorphism
space of the square has dimension 3 and isogeny preserves this
rank. The Kummer resolution adds the sixteen exceptional
classes. Hence the Picard number of the geometric surface is 19;
compare [Hulek–Schütt, §3B](https://msp.org/ant/2012/6-2/ant-v6-n2-p01-p.pdf)
for this Picard computation.

## 2. Exact fibres and geometric function-field rank

Over Qbar(N) the receiver itself has a branch point section at
t=1/(3√β); by the explicit branch coordinates in the predecessor,
its smooth fibre with that origin is J. Thus its geometric
elliptic surface is the same Kummer as in §1, not an assertion
that a genus-one torsor and its Jacobian are automatically
the same surface over Q.

For J the coefficient a₂ is 9μ−41μ² and a₄ is
16μ³(25μ−9). Its discriminant is

    Δ_J=16·16²·9² μ⁸δ²(25μ−9)².

The exact change X=c²x,Y=c³y at the two points c=0 drops
the discriminant depth from 16 to 4 and makes c₄ a unit.
The two points over μ=1 have δ=θe² of depth two; they have
discriminant depth 4 and c₄ a unit. There are four points above
μ=9/25, all simple, each with discriminant depth 2 and
c₄ a unit. The two points at infinity are good: scale the
u-line model by X=μ²x,Y=μ³y, then the discriminant is a unit.
There are no other singular fibres. Thus J has four I₄ and
four I₂, and the reducible-component rank is 16. Applying the
[Shioda–Tate formula, Corollary 6.13](https://arxiv.org/pdf/0907.0298)
gives rank 19−2−16=1. The rational 2-isogeny implies the same
geometric rank for J′; no Picard comparison across isogenies is
needed. Independently, the same elementary discriminant check
on J′ gives 2 I₂ at c=0, 2 I₈ at e=0, and 4 I₁ at μ=9/25.

## 3. Exact Galois character on the only geometric rank direction

An explicit section on J′ over Q(√β)(N), not only a rank count, is

    P: X=25μδ²,       Y=5(√β c)³ δ²(25μ+16).

It follows from the exact point x=25δ²,y=5δ²(25μ+16) on
the normalized μ-twist y²=x[x²+2(41μ−9)x+81δ²]; the elementary
square identity inside it is
25²δ²+50(41μ−9)+81=(25μ+16)².

This point is not torsion. At μ=1/2 the normalized model scales
over Q to y²=x(x²+92x+324), with P=(25,285).
The doubling formula gives x(2P)=(301/570)², so in the
integral short model with new x=9x+3·92 and new y=27y,
the double has a denominator divisible by 5. Nagell–Lutz rules
out torsion there. Specialization at this smooth fibre
commutes with multiplication, so the geometric section is
nontorsion.

The nontrivial automorphism of Q(√β)/Q sends this nonzero
rank direction to its negative: X is fixed and Y changes sign.
Since the geometric rank is exactly one, the entire
Mordell–Weil group tensored with Q has no fixed direction.
Hence the rational rank over K is zero for J′, and for J by
isogeny. In particular changing c by a rational function on the
*whole* norm conic does not produce a rational generic point of
the original genus-one receiver.

## 4. Torsion at the generic point and at every rational fibre

In the scalar Kummer map on J′, the origin has class 1 and
T₀=(0,0) has the class of (9μδ)², also 1. The explicit
P₄=(9μδ,8μ·9μδ) has double T₀ and x-class βθ. These are exact
on the entire smooth conic family. The quadratic factor of J′
has discriminant 256μ³(25μ−9); it is nonsquare over K, since
each of the four geometric zeros above μ=9/25 has odd depth.
Thus there is no generic rational involution other than T₀.
As x(2Q)=((x(Q)²−(9μδ)²)/(2y(Q)))² for y(Q)≠0, P₄
has no rational half: its class βθ is nonsquare in K, which is
a regular extension of Q. All rational 2-primary torsion over
K is therefore exactly the cyclic group generated by P₄.
Any odd-order torsion has trivial x-class in the exponent-two
Kummer quotient. Since all rational generic points are torsion,
the only generic scalar classes are 1 and βθ.

There is no rational exceptional conic point: the two points
at infinity are not real because β,θ>0; c=0 would make θ
square, e=0 would make β square, and μ=9/25 would make β
square. Thus every rational conic point has 0<μ<1 and is a smooth
fibre. At some such fibres additional rational 2-torsion can
appear. But if the quadratic factor splits rationally (and
hence really), μ>9/25 and its coefficient 2μ(41μ−9) is
positive. Both nonzero roots are therefore strictly negative
(they have positive product and negative sum). Their Kummer
classes are negative, and they cannot be doubles of rational
points by the square doubling formula. Every rational order-four
point is then ±P₄ plus rational 2-torsion. Its Kummer class is
either βθ or negative, by multiplicativity. None of these
order-four points can have a rational half, again by the square
doubling formula and nonsquareness of βθ in Q. (A rational
point with y=0 only doubles to the origin.) Odd-primary
torsion still gives class 1. So the positive torsion image at
every rational fibre is exactly {1,βθ}; neither β nor θ can
be supplied by torsion growth.

Consequently a rational point on a specialized receiver would
certify a nontorsion point of the exact J′, with exact class β
or equivalently θ. The positivity and old local address
conditions of the original marked pair still concern the
receiver's specific open; neither the rank statement nor
torsion calculation supplies an actual point there.

## 5. Exact arithmetic controls

The replay checks polynomial invariants and discriminants,
the geometric section and its integral non-torsion
specialization, and the separate rational growth example
β=3, θ=13, c=2/5, e=1/5. In that growth example J′ does have
two additional rational 2-torsion points, x=−324/625 and
−6084/625; translating its positive order-four point by
either gives a negative abscissa. This is a torsion control,
not an original Ready pole or a rational point on one of
the desired receiver fibres.

    python3 -B replay_mobius_geometry.py | cmp - EXACT-GEOMETRIC-RANK-CONTROLS.json
    sha256sum -c SHA256SUMS
