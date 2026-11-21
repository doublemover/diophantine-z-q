# Exact line-field tower and discriminants for the actual 13-Selmer field

Fix the same one-I d=2811626664334219040035976315 and curve
E_d:y²=x(x−d)(x+3d). Let F=Q(P) for the same nonzero 13-vector, and
F_x=Q(x(P)), K=Q(<P>) the intermediate sign and line fields of
degrees 84 and 14. This is explicit relative input for the faithful λ
computation in the [point-field certificate target](../actual-one-I-cyclotomic13-r1/EXACT-POINT-FIELD-13-CERTIFICATE-TARGET.md).
No ideal class eigenspace, unit basis, rank or point is computed.

## 1. Exact line polynomial and the relative tower

Put u=x(P)/d, v=13u and A=∑[13·x([2]^j P)/d : 0≤j<6].
The generator 2 has order 12 modulo 13 and [2]^6P=−P, so these are
exactly the six x-coordinates on the same line up to sign. Each
v([2]^j P) is integral by the pinned monic degree-84 polynomial.
The computation below proves A generates K. B=A/26 has minimal
monic integral polynomial

    B^14 + 28 B^13 − 819 B^12 − 243243 B^10 − 2918916 B^9
    − 23438259 B^8 − 89792352 B^7 − 229558797 B^6
    − 710468460 B^5 − 2375183889 B^4 − 4884126624 B^3
    − 5438448873 B^2 − 3072239532 B − 693879273.

The degree-6 equation of F_x over K is monic with roots those six
v coordinates. Its six coefficients in the A power basis are exact
rational arrays in ACTUAL-DEGREE14-LINE-FIELD.json. The final equation is

    W² = 13 d v(v−13)(v+39),      W=13² y(P)/d.

Hence degree 14, then 6, then 2 is an explicit presentation of the
same tower. Only the final quadratic equation depends on actual d.
For the scored odd λ, degree-14 or degree-84 class groups alone
would still be insufficient.

**Exact certification.** Use the pinned degree-84 division polynomial.
With g=u(u−1)(u+3), exact modular composition of the doubling function
D(u)=g′(u)²/(4g(u))−2−2u constructs the line sum and signed elementary
symmetric coefficients b_j of the six integral v coordinates.
Newton identities for the degree-84 polynomial give each modular
trace; divide by six for the degree-14 trace since the element is
fixed by all six relative conjugations. Recover the integers
Tr(A^i), i≤26, and Tr(A^i b_j), i≤13, by centered CRT.
The replay checks |c_i|≤728^i in the v polynomial, hence |v|<1456
for each complex root (sum the geometric series).
Thus |A|<8736 and |b_j|≤binom(6,j)1456^j. After multiplying
these trace bounds by 14, the product of the 12 listed CRT
primes exceeds twice every bound. The thirteenth prime is an
independent check. Newton identities give the monic line polynomial
and gcd with its derivative proves it squarefree, so A has 14
distinct conjugates and generates K. The exact trace pairing
in its power basis is nondegenerate; solving the 14×14 trace
system for each b_j recovers all its coefficients without a
denominator guess. Scaling A by 26 gives integral monic coefficients
as checked. Its order is not claimed maximal.

## 2. Actual field discriminants

The discriminants are positive (even complex-place counts).
The exact formulas are

    Disc(K)   = 2^14 3^12 13^13  = 2637172728176533939372032,
    Disc(F_x) = 2^98 3^72 13^83,
    Disc(F)   = 2^266 3^144 13^167 d^84.

Use the local conductor–discriminant formula for permutation
embedding modules (Serre, *Local Fields*, chapter VI): the tame
codimension is dimension minus inertia orbit count, and the Swan
term integrates the same codimension over positive upper indices.
Equivalently sum the lower terms |G_i|/|G_0| times codimension.

**At 2.** Projective torsion is unchanged by quadratic twisting; use
E₁. By potential good reduction the prime-to-2 torsion inertia acts
through automorphisms of the supersingular special elliptic curve;
see [Kraus's potential good inertia analysis](https://geodesic.mathdoc.fr/item/MM2_1990__69_1_155566/) and [Cali–Kraus for prime-to-residue-characteristic torsion differents](https://geodesic.mathdoc.fr/articles/10.4064/aa104-1-1/).
The action of the latter automorphisms on E[3] or E[13] is faithful:
an automorphism trivial on the whole p-torsion would differ from
the identity by an isogeny of degree at least p² unless zero,
whereas the endomorphism-degree parallelogram gives at most four.
Inertia has determinant one; the scalar kernel in either torsion
representation is the same intersection with {±1}.
Thus its two projective inertia actions factor through the same
image and inherit the same upper ramification filtration (over
the maximal unramified base).

The 3-torsion line polynomial of E₁ is 3x⁴+8x³−18x²−9.
After x=3+2z and division by 16 one obtains
3z⁴+22z³+54z²+54z+18, Eisenstein after making it monic by its odd
leading coefficient. Its root is a uniformizer generating the
local maximal order. The discriminant has exact 2-valuation 4,
as computed by the replay. The projective action on the four
3-lines is therefore transitive under inertia and its tame
codimension is three. Its group lies in PSL₂(F3)=A₄.
Transitivity forces order divisible by four, so the wild inertia
is V₄. Inertia cannot equal V₄ since its first positive lower
contribution would be 3, while the computed Swan term is 4−3=1.
Thus inertia is A₄ and its first wild term is already (4/12)·3=1;
all higher projective lower groups are trivial. There is one
positive projective upper break 1/3.

On P¹(F13) every nonidentity member of A₄ has two fixed lines:
lifted involutions split since −1 is a square, and lifted order-3
projective elements have eigenvalues of order dividing six.
Burnside gives three A₄-orbits and five V₄-orbits on the 14 labels;
the contribution is 11+9/3=14.
On the 84 nonzero vectors up to sign, both actions are free:
a determinant-one lift of a nonidentity projective element with
eigenvalue ±1 would be a signed 13-unipotent, impossible here.
Their contribution is (84−7)+(84−21)/3=98.

For the 168 actual vectors the full inertia is SL₂(F3), with wild
quaternion group Q₈: it contains −I since a lift of a projective
involution squares to −I. This action and that of every subgroup
is free off zero (no nonidentity eigenvalue 1 in a prime-to-13-order
determinant-one group). Up to the upper break 1/3 the wild image is
Q₈, whose subgroup cannot map bijectively to V₄. After that the
wild action, if nontrivial, is central. The actual conductor exponent
4 at 2 is the previously identified conductor-48 model twisted
by −d≡5 (mod8), unramified at 2; residual reduction preserves
the finite inertia. The two-dimensional Swan conductor is 2.
Any nontrivial wild group has codimension two, so the total
positive upper interval has length 1. The extra central interval
therefore has length 2/3. The full permutation contribution is
(168−7)+(168−21)/3+(168−84)·2/3=266.

**At 3.** Split multiplicative Tate inertia is the nontrivial
tame transvection group of order13. Its moving orbits have length
13 and the fixed labels are exactly the nonzero vectors on the
formal line (only one line for K and identifying ± for F_x).
The discriminant exponents are 12, 6·12=72, and 12·12=144.

**At 13.** Use the exact formal/nonformal decomposition from the
frozen 13-local packet. At the nonformal place the uniformizer
r=t(P−P0↑) lies over the unramified degree-12 base and has valuation
1/13 in base units. The actual convergent series
[13](r)+t([13]P0↑), not the finite truncation, has first
unit coefficient in degree13 and constant term of valuation one
by the exact mod169 result. Weierstrass preparation makes it an
integral unit times a monic Eisenstein polynomial of degree13.
At its root the derivative has normalized valuation 13:
the invariant differential gives [13]'(r)=13·h(r)/h([13](r))
with both factors units. The exact different exponent is thus
13. The Δ action at this place is faithful on the residue field,
so the different is unchanged descending through the unramified
extensions to the line and x-fields. Their nonformal residue
degrees are 1,6,12 respectively. The other local factor contributes
zero for K, 5 for F_x and 11 for F (totally tamely ramified of
degree 1,6,12). This gives 13,83,167.

At every odd prime dividing d, inertia is the central quadratic
twist −I, hence contribution zero on lines and sign pairs and
84 on vectors. All other finite primes are unramified.

## 3. Consequence for a certified calculation

The exact point discriminant has 2641 decimal digits (8772 bits).
The standard Minkowski norm bound for generating Cl(F) has
1257 digits. Its size is not a complexity lower bound for other
class-group algorithms. Relative discriminant norms are
2^70·13·d^84 over F_x and 2^98·13^11·d^84 over K. The exact tower
makes degree-14 arithmetic small and gives a path for relative
relation search using the already staged free-Δ ideal sieve.
It does not certify full projected principal relations, class
rank, or independent scored global elements.

    sha256sum -c SHA256SUMS
    python3 -B check_actual_line_field.py | cmp - ACTUAL-DEGREE14-LINE-FIELD.json
    python3 -B check_field_discriminants.py | cmp - ACTUAL-FIELD-DISCRIMINANTS.json
