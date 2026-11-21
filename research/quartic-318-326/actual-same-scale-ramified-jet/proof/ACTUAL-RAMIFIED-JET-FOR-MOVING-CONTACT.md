# A first ramified Heegner jet detects the actual moving additive coordinate

This is a finite conditional detector, not an evaluated trace.
Keep one of the actual same-scale analytic sources: the fixed base
E_* with even companion h=−9239, or Hom's lower semistable E^flat
with h=−2207 and d=rD (r=407·2399). In the first case d=D.
Use the same literal oriented conductor-one Heegner points of
that source, with its actual based map π and genus character ψ.
Write K=Q(√Δ), Δ=hd, and Qψ=∑ψ(c)π(x_c), with the same labels
and no normalization by the class number. The source identifies
Qψ as an actual anti-invariant point in E_base(Q(√d)); its
twist descent is on the same selected E_D. Take any actual
moving p|D, where p is odd, p∤hN_base r and v_p(d)=1.

## 1. An actual residue field and finite jet instead of a p-adic height

The prime of K above p has square (p) and its ideal class
has order ≤2. In the Hilbert class field there is no
additional ramification, and the residue degree at this
prime is its actual class order ≤2. Thus one completion L
containing all the terms of the trace has ramification index 2
and residue degree at most 2 over Q_p (tame auxiliary
rigidification may extend the residue field). Write ε=√d,
a uniformizer of the ramified real-twist local field inside L.
Modulo ε² the ring has characteristic p and is its residue
field with one nilpotent ε (after the canonical residue
section). The genus character source identifies the actual
trace as anti-invariant under ε↦−ε, not merely its norm.
In the good base reduction at p this involution is trivial
on the residue field of Q_p(ε), so the trace reduces to
a point killed by 2. Therefore P=[4]Qψ has residue O and
its invariant tangent at O gives a finite scalar
```
                         J_p = z_base(P)/ε mod p,
```
with z_base the formal parameter, and the quotient read as
the coefficient of ε mod ε². It actually belongs to F_p
under the anti-invariant descent to the rational twist.

On the literal twist model of good y²=x(x−s₀)(x−t₀),
the map to the base is (x,y)↦(x/d,y/(d ε)).
It gives z_base=ε(−x/y) **exactly**. At p the twist has
type I0* with all three roots at depth one; the minimal
cubic modulo p is y²=x³, and the rational two-torsion
maps onto the four components (the exact torsion parity
rows are the four distinct ones). Hence the descended
[4] point is in the nonsingular connected subgroup.
On the cubic cusp its smooth additive coordinate is
−x/y (zero at infinity); this is nonzero modulo p
precisely when its point avoids the formal subgroup.
Thus J_p is exactly the component-stripped additive
residue, with no ambiguity up to a squareclass.
Changing a minimal differential or a uniformizer
by a unit does not change the asserted nonvanishing.

Consequently J_p≠0 proves nontorsion of the original rational
descended trace: rational torsion on this twist is exactly
E_D[2] by the independent small good counts, hence [4]
would kill it. In the same actual analytic source the
fixed even companion central value is nonzero; the
conductor-one Gross–Zagier identity and odd sign give
analytic rank exactly one, and Gross–Zagier–Kolyvagin
gives arithmetic rank one and finite Sha. As reduction
of the component-stripped additive coordinate at p is
a homomorphism, a nonzero value on [4]Qψ forces the
primitive rational generator's residue also nonzero.
At p_a this is the exact missing simple-contact
orbit condition, not the full fixed-support or finite CRT.
At the other movers it is the analogous local condition.

## 2. Compute the first-order CM tangent from the already reduced oriented endomorphism

At one actual label choose the reduced oriented CM pair
(A,C_N) at the corresponding point of the good modular
curve at p. Introduce enough prime-to-p level to work on
a fine tame chart there, retaining the actual C_N. This
can be done over an unramified enlargement once the
elliptic curve has good reduction; finite étale groups
have unique lifts of the marked residue torsion data.
At a supersingular residue elliptic curve the p-divisible
group is its connected height-two group. The mod-p local
maximal O_K action is a height-one formal O_{K_p}-module.
[Gross, On canonical and quasi-canonical liftings, Prop. 2.1](https://archive.mpim-bonn.mpg.de/id/eprint/3578/1/preprint_1985_30.pdf)
gives its canonical maximal-order lift over the completed
maximal unramified extension of K_p with the prescribed
action on Lie. Serre–Tate deformation and the finite
étale prime-to-p marking identify it with the first
local jet of this **same oriented CM lift**. This is
a use of maximal-order conductor one, not a claim for
an arbitrary nonmaximal or differently oriented lift.
Passing to a larger unramified field to rigidify a
residue model changes none of the descended coefficients.

Let a_CM be the actual element √Δ in its endomorphism ring.
Its linear coefficient in a local formal parameter X is
the fixed CM-type embedding √Δ, the same for the whole
oriented class orbit. Its degree is |Δ| with p-exponent
exactly one. It reduces to an isogeny whose inseparable
degree is exactly p (zero derivative and exactly one
p-factor), so its first reduced formal coefficient is
some c in F_pbar^× times X^p. Let u=Δ/p, a signed rational
integer prime to p. In the good local lift,
[a_CM]²=[p]∘[u]. Reduce this exact identity modulo ε².
The coefficient of X^p on the left is exactly
```
                             √Δ · c .
```
Proof: all coefficients of the first endomorphism
below degree p are in (ε), its linear coefficient
is √Δ, and the residue at degree p is c. For outer
degree i≥2, any inner degree-p term forces total
degree >p, and all inner lower-degree terms give
ε^i=0. Only outer degree one survives at X^p.
On the right, characteristic p makes the derivative
of [p] identically zero by its invariant differential,
so every nonzero series degree is a multiple of p.
Its X^p coefficient, the Hasse value in this formal
trivialization, is multiplied by u^p≡u. Thus the
normalized derivative of the Hasse invariant is exactly
```
                 dHa(v_c) = c·(√Δ/ε)/u  in F_pbar,
```
where v_c is the CM point's infinitesimal displacement
relative to ε and the chosen invariant differential.
The root √Δ/ε=√h, including its sign, is the one from
the single common local oriented lift; independently
flipping it in individual summands is not allowed.

The Hasse zero is simple on a fine tame chart at every
supersingular point. For a direct check take the full
2-level Legendre chart with Hodge trivialization:
m=(p−1)/2, H(λ)=∑_j binom(m,j)^2 λ^j.
Its values at 0,1 are nonzero, and mod p it satisfies
λ(1−λ)H″+(1−2λ)H′−m²H=0.
A multiple root off 0,1 forces all derivatives to vanish
by differentiating this equation, impossible for a
nonzero polynomial of degree <p. Thus dHa determines the
one-dimensional tangent uniquely. The use of a tame
fine chart avoids any false inference from a coarse
j-coordinate ramified at 0 or 1728. The computation uses
the finite leading coefficient c of the **oriented
endomorphism**, not just its reduced j-value.

## 3. Exact weighted differential endpoint

Let ω be the invariant differential on the good base
chosen so that it agrees with dz_base at O. On points
over dual numbers, the linear part of the group sum is
the sum of the individual invariant tangent values;
translation and the base-point constants contribute
nothing to that tangent. Hence
```
                    J_p = 4 ∑_c ψ(c) (π^*ω)(v_c).
```
All terms use the same actual modular map and the same
oriented reduced level, and the same common uniformizer.
The literal differential is required; a newform multiple
may replace it only after its actual scalar is accounted
for at p. In particular no cancellation of class labels,
local norm, or factor depending on the order of an
isogeny has been inserted.

This reduces the required modulo-ε² calculation to
finite reduced oriented endomorphism leading coefficients
and modular differential evaluations. It does **not**
enumerate the class group, construct that modular
projection, evaluate the sum, or assert a fast algorithm.
The existing order-17 mod-61 test is different: here a
nonzero first ramified jet would certify both nontorsion
and the specifically missing p-primary local residue.
It would still not supply remaining contacts, the
simultaneous odd-multiplier CRT, or a PointPair.
