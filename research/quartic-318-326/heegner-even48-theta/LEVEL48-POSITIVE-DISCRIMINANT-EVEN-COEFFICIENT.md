# An explicit independently calibrated even coefficient at level 48

**Claim and scope.** Let D be positive, squarefree, D ≡ 13 (mod 24).
For E_t : y²=x(x−t)(x+3t), put
N_*(D) = √D L(E_(−D),1)/|Ω_pr^+(E_(−1))|, with the primitive
real period, not total real Néron volume. The two small scripts in
this directory define a signed integral coefficient A(D); the
identity is

    N_*(D) = A(D)^2 / 32.

In particular this computes exactly the even genus-partner central
quantity in the primitive convention for d ≡11 mod24, m ≡23 mod24
and D=md squarefree. It is independent of the 13-adic *odd trace*
and the higher level 2544, and does not supply an actual selected
scalar h, theta, or proof of paired nonvanishing. The present brute
force enumerator is for bounded examples only.

## Modular form and auxiliary character

Use the genuine rational normalized f48 of E_(−1), whose minimal
equation in the fixed chart is y²=x(x+1)(x−3). At 3 the tangent
x²(x+1) is split so U3=+1 and W3=−1. The root number is +1
(e.g. the exact Fricke of the genuine low-level map), so W16=+1.
For positive fundamental D≡13 mod24, its local type at (∞;2,3)
is gamma=(+;−,+). Sirolli–Tornaría Eq. (9.1) reads
(+1)(−1)^4(−1)(+1)=−gamma(∞), as needed. At the only
odd level-exponent prime 3 take B ramified at {3,∞} and
take the Eichler order R of level 16 in a maximal order.
For gamma, the type-II function is required only at 3 with χ3;
there is no type II at 2. Use l=−19 (a fundamental discriminant),
which has (l/2)=−1 and (l/3)=−1, satisfying the opposite
sign at the division prime. Its central value is nonzero:
L(f48⊗χ_l,1)=L(E_19,1), and Feng–Liu–Pan–Tian Thm. 2.7
gives odd analytic Sha for 19≡7 mod12 since h(−19)=1
(the unique reduced form is (1,1,5)). This is unconditional
analytic nonvanishing, not an appeal to BSD. Their separate
displayed Thm. 2.8 diagonal formulas for n≡3,7 mod24 do NOT
cover D≡13. The ST new form is holomorphic of level
4·lcm(48,3²)=576. In applying ST Thm. 9.2 to a fundamental
D sharing 19 with l, use the stated theorem as proved
by Prop. 8.1 and the final paragraph of the proof of B:
the initial coprimality in Thm. 6.3 is not imposed at the end.

Primary references: [FLPT §§2.2–2.3](https://arxiv.org/html/2405.11132v1#S2)
and [ST §§4–6,8–9](https://arxiv.org/html/2107.04483).

## Actual quaternion input, not a guessed weight space

Take ω²+ω+1=0, i²=−1, iω=ω̄i. Then
B=(−1,−3) and O=Z[ω] + Z[ω] i has reduced discriminant
3 by its trace pairing, hence is maximal. The maximal
order has one ideal class (equivalently the unique
geometric characteristic-3 supersingular j=0 by the
Deuring ideal-class correspondence). For example the
presentation realizes the endomorphisms on y²=x³−x
via an order-three translation x↦x+1 and the order-four
map (x,y)↦(−x,√−1 y), plus this discriminant check.
Thus the right R-class set is identified with the
O^×-orbits of cyclic direct summands of rank one in
(Z/16)². Indeed with the unique maximal class, all
adèles lie in Ř^×\Ō^×/O^×; the only level mark is at 2.
Equivalently a class representative x is integral unit
away from the original local subgroup, with x_p=1 for
p≠2, and can be chosen so that its inverse sends the
standard line to the chosen marked line.

In Z₂[ω], lift u≡1+6ω mod16 to norm −1
by Hensel (the derivative in the ω-coordinate is odd).
Realize ω by multiplication, and i by v↦u·v̄. The
map is an isomorphism to M₂(Z₂), since mod2 identity
and conjugation are linearly independent over F₄
(test at 1 and ω), and both lattices have rank 4.
This supplies the genuine split level condition independent
of the choice of a lifted u. Enumerate all 24 cyclic
lines mod16. The 12 norm-one elements act with four
orbits of size 6, representatives (0,1),(1,2),(1,4),(1,8)
in basis (1,ω); each line stabilizer is ±1, so the
height/θ sum factor t_x of ST (3.1),(5.10) equals 1.
To compute T_q, enumerate O elements of norm q
(q prime to 6), take their actual action on the mark,
and divide multiplicities by 12 for the O^× quotient
of the q-neighbors. This is exactly the usual norm-q
correspondence in the single maximal class. Whether one
restores the class by α or its projective inverse makes
no difference to the full array: conjugation α↦ᾱ
preserves the full set. The complete T5 and T11 checks
already isolate the unique relevant eigenline, because
T11−eigenvalue −4 forces first two coordinates equal
and last two equal, then T5−eigenvalue −2 forces the
sum zero. Thus JL for the actual Steinberg factor at 3,
whose exact f48 traces at q=5,11 are −2,−4 by direct
point counts, pins φ=(1,1,−1,−1), up to global sign.
The computed uniformizer 1+2ω has sign + on φ, matching
U3; at this local normalizer δ^{l,χ}=(l/3)·(−1)=+1.
The rank-four computation records further selected q
only as checks, not as a substitute for JL.

## Literal weighted lattice equation

For each matched representative v define R_v as the
suborder of O preserving its cyclic line under the
above representation mod16; this is precisely the
ST R_x=x^{-1} R x local conjugation. All four adèles
are 1 at 3 and 19, integral units at 2, so the
transport factor χ^l(Nx) is 1, the two local weights
are the same functions on O/ℤ, and t_x=1. In basis
(ω,i,ωi) for O/ℤ the discriminant is

    Δ(B,C,E) = −3B²−4(C²−CE+E²).

For type II at3 use z=i and the polarized Δ.
The quotient <y,i>/<i,i> reduces to C+E at 3,
so the weight is the quadratic symbol (C+E / 3),
including 0. For type I at19 use nonzero isotropic
z=(0,1,8) mod19 and set <y,z>=Δ(y+z)−Δ(y)−Δ(z):
the weight is 0 on the zero class or off the isotropic
cone, (−<y,z>/19) if the bilinear form is nonzero,
and (a/19) if y≡az on the isotropic cone orthogonal
to z. This is exactly ST (4.1–4.5); changing the
initial isotropic z only gives a common sign. There
is no holomorphic unit conversion at infinity
because l<0. The lattice coefficient in ST (5.2)
for fundamental D is over y with Δ(y)=−19D, not
the unmarked norm of quaternion elements themselves.
All ideals called a,b,c in ST (5.2) are the unit
ideal here since l,D are fundamental integers.
The script only adds y belonging to the chosen
R_v/ℤ, tested by the 2×2 column determinant modulo
16 (no invertibility of the image is needed).
Combining the four lattice sums against φ gives
A(D), literally the ST (5.10) coefficient up to
the global sign. ST normalizations that use an
overall nonzero factor cancel in the next ratio.

## Calibration and exact scope of the formula

At D0=146965=455*323, enumeration gives per-class
weighted sums (64,64,−64,−64) before multiplying by φ;
A(D0)=256. The independently sourced cusp-cycle
and exact Mellin-interval certificate
EXACT-EVEN-CENTRAL-LATTICE-455-DISPLAY.md fixes
N_*(D0)=2048 for exactly this curve and period.
In ST Thm. 9.2 the common normalizing constant,
Hecke vector and gamma are fixed, and there is no
2^{ω(D,48)} factor since D and 48 are coprime.
Thus multiplying the quotient of the exact central
values by √(D/D0) cancels the square roots and gives
N_*(D)=2048·(A(D)/256)²=A(D)²/32. The imaginary
period on E_d equals |Ω_pr^+(E_(−1))|/√d by the
literal twist maps. Consequently V13's primitive
even companion value √m·L(E_(−md),1)/|Ω_pr^−(E_d)|
is the same quantity. A separately changed K14 fixed
rational period multiplier would change the valuation
accordingly; no moving factor has been inserted.

The exact coefficient gives a zero/nonzero decision
and, if nonzero, ν₂=2·ν₂(A(D))−5 without BSD. It
does not imply the odd trace mod13 is nonzero (that
requires the distinct higher-level lift), and does not
produce the later independent even addressed graph
supply. At 68+ digits a straightforward enumeration
here is infeasible. Diagonalizing and solving the
binary Eisenstein norm by factorizations per B gives
a smaller asymptotic algorithm, but still no claim
to have evaluated an unspecified or astronomical
selected tuple. Small controls deliberately include
a nonfundamental D=325; its raw coefficient is just
a script test, not within the theorem.

Reproduce:
  python even48_brandt.py
  python even48_coefficient.py 13 37 61 85 109 133 157 181 205 229 253 277 301 325 146965
