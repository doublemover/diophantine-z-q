# Exact local 13-conditions and a single global eigenspace certificate target

This is the literal historical one-I curve
`E=E_d:y²=x(x−d)(x+3d)`, for
`d=2811626664334219040035976315` and original q=119851.
It does not evaluate its 13-Selmer group or prove rank one. It
reduces one concrete sufficient upper-bound certificate to an exact
single eigenspace of one explicit field, with minimal local controls.

## 1. Every original bad prime has zero local H¹

Write V=E[13]. At 2 and at the ten odd primes dividing d, the
minimal model has additive reduction: at odd d-primes the reduced
cubic is y²=x³ with discriminant valuation 6, and at 2 the cusp in
the displayed integral model has discriminant valuation 8 (<12).
The component group for additive elliptic reduction has order
at most 4. The nonsingular reduced group has order the residue
characteristic. Thus there is no 13-torsion in E(Q_l); the formal
open pro-l subgroup is prime-to-13 divisible. At 3 the reduction is
split multiplicative I₂: its tangent coefficient −d is 1 mod 3,
and its Tate parameter has valuation 2. The valuation quotient
and the residue units both have order 2, and no 13-torsion remains.
The invariants of V vanish at all these finite bad places.
Weil self-duality and local Tate duality give H²=0, and the local
Euler characteristic at l≠13 gives H¹(Q_l,V)=0 as well.
At infinity H¹ is zero because the real Galois group has order two.

At a good prime away from 13 the local condition is unramified.
At 13 the exact good reduced count is 16 and a13=−2, a unit not
equal to 1 mod 13. The unramified quotient V⁻ has Frobenius
character ψ with value −2, of order 12. The ordinary formal
line is V⁺=μ₁₃ ⊗ ψ⁻¹ by the Weil pairing.
Then H⁰(V)=0 and H²(V)=0, so H¹(Q₁₃,V) has dimension 2.
For each of V⁺, V⁻ the invariants and dual invariants are zero,
so the dimensions of their two H¹'s are each one. Hence
H¹(V⁺) injects into H¹(V), giving a one-dimensional kernel
of the map to H¹(V⁻).

The formal elliptic subgroup equals the p-adic logarithm lattice
13·Z₁₃ (log congruent to the formal parameter modulo 13²).
Since the residue order 16 is prime to 13, the local Kummer image
has dimension one and is exactly the just named formal H¹ line:
a [13]-preimage of a formal point can be chosen in the formal
locus over an algebraic extension. A possible actual generator
P_1 is the formal point with t=−x/y=13, from the unique Hensel
root z=-1/y of `z=t³+2d·t²z−3d²·t z²`. Its formal logarithm
is a generator of 13·Z₁₃ modulo 13²·Z₁₃. This is a genuine
local point, not a global rational point.

## 2. Exact ordinary splitting/inertia and point-field orbits

In the unramified degree-12 extension of Q₁₃ use the ring
`(Z/169)[T]/(T^12+2)` modulo 169. The residue polynomial is
irreducible. The exact arithmetic in the replay obtains a
reduced order-13 point

```
x0=8+4 T²+5 T⁸,     y0=4 T³+9 T⁹    over F_(13^12).
```

The verifier computes the cardinality
23,298,094,520,064 by the exact Frobenius recurrence, chooses
and verifies this nonzero reduced generator, lifts the y-coordinate
by Hensel while fixing x, and computes [12] of the lift by
invertible affine denominators. In the final addition of the lift
and [12] times it, the x-difference B is divisible by 13,
the y-difference A is a unit. Write
`C=A²−B²(a2+x1+x2)` and
`D=A(x1 B²−C)−y1 B³`. Then the formal t of the sum is
`−BC/D` and D is a unit, so numerator division by the
nonunit B is never taken. The result is

```
t([13] lifted P0)/13 = 4 T mod 13.
```

Consequently P0 does not lift to rational 13-torsion in the
unramified degree-12 extension: replacing its lift by a formal
point can only change [13] of it by an element of the second
formal neighborhood. For a control, changing a4 by 117
preserves the reduced curve and gives word zero by the same
arithmetic, a genuine alternate local situation. In that case
one can subtract a formal [13]-preimage of the return point.
For the actual model it is nonzero.

Inertial action on V⁺ contains the whole mod-13 cyclotomic group
of order 12, while its quotient action is trivial. If the
wild unipotent group were absent, the prime-to-13 inertia
representation would split and have an invariant outside V⁺.
That invariant line lifts the reduced étale line, with
Frobenius order 12. Its generator would be defined over the
above unramified degree-12 extension, contradicting the
exact test. (Equivalently, any unramified torsion lift of
the same reduction is unique, since V⁺ has no inertia
invariants.) Thus inertia is the full affine subgroup of
order 156, and the decomposition group is the full upper
Borel, since its unramified quotient ψ has order 12.

Let L be the full 13-torsion field and F=Q(P) the field of one
nonzero vector, of degree 168 by the known full GL₂ image.
The exact Borel actions on the 168 labels give two primes
above 13 in F:
- The orbit of 12 **nonzero formal** vectors is one inertia orbit:
  (e,f)=(12,1).
- The other 156 vectors form one decomposition orbit and 12 inertia
  orbits encoded by their nonzero étale coordinate. Inertia translates
  the first coordinate freely: (e,f)=(13,12).

Write these primes w+,w−. For optional local power-class
calculation suffices a unit modulus of exponent respectively
14 and 15: for absolute ramification e over Q₁₃, any unit
at depth `e+floor(e/12)+1` is a 13th power by the logarithm
at depth `floor(e/12)+1`. These are explicit local caps on
this point field, not 156-based caps on the full splitting field.

## 3. Exact small width of a sufficient point-field computation

Set F_B=Q(<P>), the degree-14 field of its line. F/F_B is cyclic
of degree 12, with Δ acting by point scalars. Fix the character
λ:Δ→F₁₃× taking an element to its actual scalar on P.

There is an injection of global H¹(Q,V), hence of Sel₁₃, into
the λ-eigenspace of F×/F×¹³. Take restriction to F and evaluate
by the literal Weil pairing c↦e₁₃(c,P). If it vanishes, restrict
to L, where the cochain is a homomorphism; its image is contained
in the line spanned by P. By Galois equivariance and irreducibility
it vanishes. Inflation–restriction then gives zero already over
Q: H¹(GL₂(F₁₃),V)=0 by the central scalar −I (its difference
from the identity is invertible). For the sign of the eigenspace,
applying g∈Δ to the local pairing sends P to λ(g)P and the
restriction of the global class to the same cohomology class;
so the eigencharacter is λ, not its inverse.

Every Selmer element in that image is in the global Kummer group
F(S,13), where S consists only of the two primes over 13:
all other valuations are multiples of 13, by unramifiedness
at good primes and the original zero local class at bad primes.
Thus, after taking λ-eigenspaces, the exact Kummer sequence is

```
0 → (O_(F,S)^×/13)_λ → F(S,13)_λ → Cl(O_(F,S))[13]_λ → 0.
```

The unit term has dimension **7**. Complex conjugation on
V has eigenvalues 1,-1, so F has 12 real and 78 complex places;
the line field has two real and six complex places. Above the
real place of the +1-line the archimedean places give a regular
Δ orbit; above that of the −1-line they give Δ/{±1} and no
contribution of the odd λ. Every complex base place gives one
regular orbit. The trivial product relation does not change
a nontrivial eigenspace. Dirichlet's unit theorem and
prime-to-13 semisimplicity give the same λ multiplicity modulo
13 as in the regular-orbit character. The global field F has
no μ₁₃: the subgroup fixing one nonzero vector still has
surjective determinant. Both primes over 13 are individually
fixed by Δ, since the two types of Borel orbits belong to
different line-field places, so adding S changes only the
trivial character. Also, quotienting the class group by
those two ideal classes changes only the trivial character.
Thus the remaining class-group width is exactly
r=dim Cl(F)[13]_λ, unknown.

Here are the effective local constraints for an upper bound
on the image of Sel₁₃ inside that (7+r)-dimensional space.
- At an odd prime dividing d, scalar −I is actual inertia
  on V (the ramified quadratic twist of good reduction).
  At 2 it is also inertia: the actual conductor exponent at 2
  is 4 (unramified twist of the conductor-48 curve), so the
  potentially good inertia has nontrivial wild 2-group.
  This survives mod 13, and its order-two element in SL₂(F₁₃)
  must be −I; determinant is unramified at 2. Hence in
  F/F_B the element −1 is inertia at each place over these primes.
  It acts trivially on the valuation line and residue-unit
  Kummer group over l≠13. Since λ(−1)=−1, the λ part restricts
  to zero automatically at all these primes.
- At 3, the local split Tate action has upper transvections of
  order 13 and diagonal Frobenius of order 3 on the formal line
  (3³=1 mod 13), quotient trivial. The four formal-orbit
  completions have (e,f)=(1,3); their residue units of order
  divisible by 13 yield one λ restriction in aggregate.
  The other twelve completions have (e,f)=(13,1), no residue-unit
  13-quotients, and their valuations are zero in the S-Kummer
  group already. Thus only one scored λ unit test remains at 3.
- At w+ the real ordinary local Kummer line evaluates to zero
  under Weil pairing with a formal 13-vector. At w− it evaluates
  to a line, in fact nonzero as explained below. The local λ
  target dimensions are respectively 1 and 13: use the additive
  normal-basis representation on the untorsioned local unit
  logarithm and the fact that each local degree over F_B is
  12. There is no local μ₁₃ at w− because e=13; at w+ its
  point stabilizer has determinant still surjective (ψ primitive,
  choose Frobenius and adjust inertia to fix the formal vector).
  Valuation lines are Δ-trivial. Consequently a usable small
  upper-bound test consists of a scalar at 3, the scalar at
  w+, and the 13-dimensional target at w− modulo the ordinary
  line (dimension 12). Even dropping the latter line test
  still gives a valid but weaker upper bound.

For nonzero at w−, base change first to the unramified
degree-12 local field k'. Over it V⁺ identifies with μ₁₃,
V⁻ is trivial, and adjoining one nonformal point is the
degree-13 Kummer-root field of the ordinary extension class.
That class, viewed in H¹(k',μ₁₃), is in the ψ²-eigenspace
for the degree-12 Frobenius action: the original extension
lies in H¹(Q₁₃,Hom(V⁻,V⁺))=H¹(Q₁₃,μ₁₃⊗ψ⁻²).
By contrast the Kummer line of the actual local elliptic group
lies in the ψ-eigenspace there. These are distinct because ψ
has order 12. The kernel of restriction to the nonformal
point field is exactly the span of the extension class;
this follows after adjoining μ₁₃ (degree 12 prime to 13)
from the cyclic degree-13 Kummer extension. Restriction from
Q₁₃ to k' is injective on the own local line, also prime-to-13.
It therefore remains nonzero at w−, where Weil evaluation is
the chosen isomorphism of the formal line with μ₁₃. An
arithmetic model can use the formal point t=13 to produce it;
the above is a statement of its exact origin, not a precomputed
vector of basis coordinates for that field.

## 4. Presentation and the first actual remaining bottleneck

The code uses the literal division polynomial f=ψ₁₃(u) of
E₁ in x=u, so deg(f)=84 and leading coefficient is 13.
Twist x=d u and put v=13 u; the supplied integral polynomial
`13^83 f(v/13)` is monic. Put W=13² y/d. Then an exact
presentation is

```
F = Q[v,W] / (13^83 f(v/13), W²−13d v(v−13)(v+39)).
```

It requires no construction of the degree-26208 splitting
field. The Δ generator [2] is arithmetic with quotient
g(u)=u(u−1)(u+3): u' = g'(u)²/(4g(u))−2−2u, and
W'/W = −1+g'(u)(u−u')/(2g(u)). The script verifies the
radicand identity in the presented field. In particular
[2]^6=[−1] fixes u and changes W's sign, giving a quadratic
relative class-group target over the fixed degree-84 x-field;
this fixed field does not depend on d. The target is the
λ eigenspace of that relative **anti** part (one of the
faithful characters of Δ), not the whole 13-class group.
Taking 13-class groups of proper intermediate subfields
over F_B does not by itself bound the faithful λ part:
prime-to-13 extension and norm identify their images with
the corresponding invariant spaces, whereas λ has no
invariants under any nontrivial subgroup of Δ.

A completely exact sufficient certificate would give a true
(7+r)-dimensional λ basis for F(S,13), with certified λ class
generation/relations, and show rank at least 6+r for the
local conditions above (or a stronger true matrix).
No general Sha finiteness is needed. This is smaller than
a full ray-class calculation in the whole splitting field:
one relative eigenspace, exact local moduli caps at 13,
one aggregate residue test at 3, and no d-prime ray moduli.
Nevertheless the 168-degree field's discriminant retains the
factor d^84, and no certified λ class-group rank or local
global-basis matrix has yet been computed. A relation sieve
with unverified generators or an assumed P-adic BSD valuation
would not fill this step.

If that upper bound is ever produced, parity (actual sign −1)
makes full s₁₃=1, and [Yan–Zhu, Theorem 5.11](https://arxiv.org/html/2412.20078v4#S5.SS3)
gives analytic rank one at this ordinary prime, with the usual
forward rational rank and finite Sha conclusions. No such point
or odd nonvanishing has been concluded here.
