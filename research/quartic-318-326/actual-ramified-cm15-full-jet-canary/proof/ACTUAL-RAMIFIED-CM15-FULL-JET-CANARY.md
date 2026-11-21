# An exact full ramified Heegner jet: X₀(32), Δ=−15, p=5

This is a true signed **whole** Hilbert class trace through a
based modular map, not only the orientation test for a CM
endomorphism. It is a small independent check of the jet
method in 93ac9e7f and of its component-stripped rational
interpretation in f84c782f. It does not use a floating-point
CM value, a guessed reduction label, a claimed modular
projection at level 205042530, or the 2-converse.

Fix ε=√5, ρ=√−3, and √Δ=ερ. The two signs for the
horizontal 2-orientation give the same answer below
for the displayed ordinate convention. Reversing the
one common sign of the modular-map coordinates changes
J₅ by sign, not its nonvanishing.

## 1. The literal two oriented Hilbert labels

The fundamental discriminant Δ=−15 has exactly two
reduced forms [1,1,4] and [2,1,2] (the opposite sign in
the second is the boundary duplicate). Its Hilbert
class field is H=Q(ε,ρ). The exact two singular j-values
are j±=(−191025±85995ε)/2; see the primary
[Kumar–Kuwata Example 9.3](https://www.cambridge.org/core/journals/nagoya-mathematical-journal/article/elliptic-k3-surfaces-associated-with-the-product-of-two-elliptic-curves-mordellweil-lattices-and-their-fields-of-definition/A5C4A0F2BA2DD613BBA2A5B83181DB86).
Here 2 splits because Δ≡1 mod8. Neither prime over 2
is principal: (x²+15y²)/4=2 has no integer solution
with x≡y mod2. Thus both horizontal 2-isogenies on
either class reach the other class. Follow one fixed
prime over 2 throughout the five steps; its fifth
kernel is the cyclic C₃₂ of the conductor-one point.
The other direction is the conjugate level
orientation, not a new class at fixed orientation.

For n=2,4,8,16 let Tₙ be Maier's normalized reciprocal
Hauptmodul (scale 4096, 256, 32, 8 of the inverse
of his tₙ, respectively). The four exact eta
products are, with [d]=η(dz),

    T₂  = [1]^24/[2]^24
    T₄  = [1]^8/[4]^8
    T₈  = [1]^4[4]^2/([2]^2[8]^4)
    T₁₆ = [1]^2[8]/([2][16]^2).

Their poles are simple and only at the infinity cusp
of their respective genus-zero curves. The two j-maps
at level 2 are (T₂+256)^3/T₂² and (T₂+16)^3/T₂
in the indicated source/target order. The exact
first-arm horizontal T₂ values over j+ are

    u± = (−49−21ε ± (495+231ε)ρ)/4.

They are distinct and both land at j−. The replay
identifies the third root of the source equation and
checks it does not land at j−. The dual T₂ at the
other vertex is 4096/u, so the non-backtracking
next step is v±=4096/u∓. The same check shows
v±=σ(u±), where σ fixes √Δ and negates ε and ρ.
The five directed steps, for either orientation,
are therefore (u,v,u,v,u), not a path that sometimes
switches the prime over 2. Degree-two horizontals
with target j in this discriminant cannot be
nonhorizontal arrows with the same target CM order.

For successive levels let A=Tₙ(z), B=Tₙ(2z) and
C=T₂ₙ(z). The true identities are

    C²=A(C+h),       C(C+k)=B,
    (n,h,k)=(2,16,16),(4,4,8),(8,2,4).

See [Maier, Tables 2,4](https://arxiv.org/pdf/math/0611041#page=11)
for the functions, cusp values and the first j-map.
The replay independently verifies all six
degeneracy identities by q-expansion. This
also certifies the +8, not +4, in T₄(2z) as a
function of T₈. Each map and candidate rational
expression has polar divisor of degree two,
so the difference of each pair has at most four
poles with multiplicities. The q-expansion
identity through degree nine after multiplying
by the appropriate q-powers gives a zero of
order greater than four, proving identity.
Thus C=(B−hA)/(A+k) is evaluated in the actual
ordered window, with every denominator nonzero
in this case. Iterating gives both T₁₆(z) and
T₁₆(2z), not an unoriented search on j.

## 2. Exact based map, signed trace, and independent rational check

By [Tian, Proposition 2.1](https://archive.ymsc.tsinghua.edu.cn/pacm_download/232/8762-35_Ye_Tian_Congruent_Numbers_and_Heegner_Points.pdf#page=6),
the pointed X₀(32) is E′:Y²=X³+4X, with infinity
O and cusp 0=(2,4), and cusps exactly E′[(1+i)^3].
On this literal model X=T₁₆(2z)+2. To pin its
normalization without a differential choice:
T₁₆(2z) is the degree-two degeneracy coordinate
with a double pole at infinity, hence X=2+A T₁₆(2z)
for A∈Q× (its value at cusp 0 is 0).
The two nonreal cusp values of T₁₆ are −2±2i
from the reciprocal of Maier's table values;
each has a cusp above on X₀(32). The only nonreal
X cusp values are ±2i by Tian, forcing A=1.

For the plus orientation this gives the first
actual known label, and its rational σ-conjugate is
the second actual known label, as follows:

    X  = (−1−3ρ+ε(1−ρ))/4,   Y=(1+ερ)/2,
    Xσ = (−1+3ρ+ε(−1−ρ))/4,  Yσ=Y.

The opposite 2-orientation replaces ρ by −ρ
in both formulas. The actual ordinate of
the first label is one of ±Y. Since σ fixes Y,
both terms use the same common sign; no fresh
arbitrary sign is chosen for the second label.
This is Artin reciprocity on the fixed oriented
conductor-one pair. The common sign allowed
here merely changes all resulting traces by
[−1]. We report the displayed +Y convention.

The nontrivial character χ of Cl(O_Δ) is the
one cut out by H=K(√5). For either orientation
the exact group-law difference P−σP is
(1,ε) on X₀(32). Use the based modular isogeny

    π(X,Y)=((X+4/X)/4, Y(1−4/X²)/8)

onto E:y²=x³−x, extending the kernel O,(0,0)
in the usual way. It is the exact rational
degree-two quotient followed by scale, and
pulls back dx/(2y) to 2dX/(2Y).
The signed full trace and its rational 5-twist are

    Qχ = (5/4,−3ε/8) on E,
    Pχ = (25/4,−75/8) on y²=x³−25x.

The independent exact [4] group-law calculation
in that rational twist gives

    [4]Pχ = (11183412793921/2234116132416,
             −1791076534232245919/3339324446657665536).

It is in the smooth cusp group modulo 5, at
(1,1) with cusp parameter −x/y≡4. This is
nonzero. It is also visibly not a 2-torsion
point before multiplication; if needed, testing
good primes 3 and 7 gives torsion order dividing
4 and all four rational 2-torsion already present.

## 3. The same jet directly from the two modular differentials

At 5 unramified ρ has residue squared 2 in F₂₅,
while ε generates the ramified maximal ideal
and satisfies ε²=0 to first order. Both Y
values have residue 1/2. The two evaluations of
the literal tangent, with parameter ε, are

    (dX/(2Y))(v₁) = (1−ρ)/4,
    (dX/(2Y))(v₂) = (−1−ρ)/4.

The character weights are +1,−1. Multiplication
by 4 kills the residue (the original trace
reduces to the rational 2-torsion (0,0));
its addition derivative is the literal sum
of the invariant tangent values at the separate
terms. Thus the normalized first jet is

    J₅ = 4·2·((1−ρ)/4−(−1−ρ)/4) = 4 in F₅,

in exact agreement with the independent
rational cusp calculation. For the residue
Frobenius pairing this is the sum of the
conjugate tangent values, not their cancellation:
σ fixes √Δ and acts by −1 on ε. The local degree
is unramified 2 over Q₅(ε), and the σ character
is −1, equivalently (−3/5)=−1.

## 4. Independent reduction of the oriented endomorphism on the same first arm

This extra check reconstructs the reduced [√Δ]
coefficient without importing the predicted
Hasse answer. Work over the characteristic-five
first-order ring F₂₅[ε]/(ε²), ρ²=2. A short
equation for the lifted elliptic curve underlying
the marked CM point can be normalized to

    η²=ξ³+Aξ+1,
    A=ε(1−ρ).

Indeed the B-coefficient is a unit at the
supersingular j=0 point and can be scaled to
one over a tame unramified extension;
let R reduce to −1 for the first kernel's
x-coordinate, adjusting the residual cube root
in the normalization. The ordered T₂ identity
for a short curve with kernel R is
256b/(a²−4b), where a=3R,b=3R²+A
(as checked directly from the j-maps). Its
first-order value is −256+256A/R².
Comparing with the exact first T₂ above
therefore gives the displayed A, since R²≡1.
The correct order-four branch from T₄ is
v=ξ(P₄)−R≡3ρ. Now in this first-order ring

    R=−1+ε(1−ρ)/3,   v=3ρ+ε(1+2ρ),   b₁=3R²+A=v²,
    R₂=R+2v,   A₁=A−5b₁,   B₁=1−7Rb₁,
    b₂=3R₂²+A₁,  A₂=A₁−5b₂, B₂=B₁−7R₂b₂=4+ερ.

These are the two normalized short Vélu
quotients (R₂ is the actual image kernel
coordinate) along the original marked cyclic-4
kernel. The exact ring check gives A₂=s⁴A and
B₂=s⁶ with s=(1−ερ)/2, *not* with
s=(1+ερ)/2. The lift corresponding to this
principal 2²-ideal is Ω=(1−√Δ)/2 with the
convention s₀=1/2. To see uniqueness,
both choices of the prime-square generator
are (1±√Δ)/2 up to sign (norm 4, not [2]);
choosing residue 1/2 removes this sign, and
the sixth-power derivative 6s₀^5 is a unit,
so the displayed B₂ decides the remaining
CM orientation. No sign is assigned
from a bare absolute value of the differential.

For reduced z=−ξ/η, a normalized short
2-isogeny with coefficient b has expansion

    z ↦ z + 2b z⁵ + O(z⁷),

by X′=ξ+b/(ξ−R), Y′=η(1−b/(ξ−R)²).
Over the reduced j=0 curve the formal
group law is plain addition to degree 5:
the sixth roots of unity scale z, so the
next possible total degree is 7. The final
isomorphism of differential s₀=1/2 scales z
by s₀. Consequently [√Δ]=[1]−[2]Ω has
first reduced coefficient

    c=−2(b₁+b₂) mod ε = 1+2ρ at z⁵.

It is nonzero. The formula from the ramified
jet proof predicts for the Hasse invariant's
first coefficient exactly cρ/(−3). The
direct Hasse invariant is the coefficient of
ξ⁴ of (ξ³+Aξ+1)², namely 2A; both give
2(1−ρ) as coefficient of ε. This final check
uses the same local oriented degree-four map,
not the previously checked different Δ=−7
curve or an unoriented Frobenius assignment.

## 5. Exact production boundary

What this demonstrates is the full finite chain
on a genuine ramified CM trace: two actual
oriented class points, a literal based modular map,
noncanceling signed cotangent terms, rational
twist descent, and agreement with the additive
group coordinate. All finite computations replay
using only Python's standard library. The facts
about the complex modular curves and class
labels have the separate short paper proofs above.

It does **not** substitute these level 32,
discriminant −15 inputs for the lower selected
target Eflat of conductor 205042530, Δ=−2207·976393·D.
For that target one must still select and certify
the literal D, find its oriented CM pair/class
roster, and evaluate the actual normalized
weight-two differential on those labels. One such
nonzero ramified jet could give unconditional
rank one via the known even companion and
Gross–Zagier–Kolyvagin; all four additive checks
are separate requirements for the four prescribed
p² cells. None of those four actual target jets,
the fixed higher pointed bound, or the unseen
odd contacts of the remaining factors is
computed here. Neither original branch changes.

Replay:

    python3 -B check_actual_cm15_jet.py | cmp - EXACT-RAMIFIED-CM15-JET.json
    sha256sum -c SHA256SUMS
