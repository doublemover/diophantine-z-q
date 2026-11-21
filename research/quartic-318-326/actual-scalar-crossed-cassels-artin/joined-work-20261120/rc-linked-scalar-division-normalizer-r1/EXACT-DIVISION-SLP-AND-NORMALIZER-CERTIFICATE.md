# Exact modular division recurrence and a normalized τ verification interface

Retain the literal fixed scalar h,J and translated i=mh, the curve
E:y²=x³−d²x, d=3−√2, and its actual raw point
P=(1+√2,2√2). Use R,β,A and N,Q,W without changing the
source labels. This note gives a modular recurrence that does not
expand either elliptic point, as well as a proof certificate for the
one remaining integer normalization. It supplies no globally
reduced values or positive candidate τ.

## Primitive chart coordinates from division polynomials

For the usual division polynomials at P put

    φ_n=x(P) ψ_n²−ψ_(n+1) ψ_(n−1),
    ω_n=(ψ_(n+2) ψ_(n−1)²−ψ_(n−2) ψ_(n+1)²)/(4y(P)),
    a_n=(2ω_n)ψ_n,       b_n=φ_n²+d²ψ_n⁴.

Then x([n]P)=φ_n/ψ_n², y([n]P)=ω_n/ψ_n³, and the exact
u-chart U_n=2y([n]P)/(x([n]P)²+d²) is a_n/b_n. Each a_n,b_n
is an integer pair in Z[√2], since 2ω_n needs no division
when written in terms of the normalized even ψ polynomials.

At good odd places (outside 2 and 7), the actual raw point is
integral, affine and nonsingular; [n]P is not identically
O since the raw point is non-torsion. The common-cancellation
exponent for φ_n,ψ_n² is zero by
[Naskręcki–Verzobio, Prop. 3.9](https://doi.org/10.1017/prm.2024.7)
(applies to an affine point of nonsingular reduction).
If ψ_n vanishes in the residue field, φ_n is a unit, so b_n
is a unit. Otherwise [n]P is affine: at an a_n zero the
ordinate vanishes and x is 0 or ±d, and at a b_n zero
x²=−d² forces the ordinate nonzero. These arguments use
d a unit and p odd. Hence a_n,b_n are primitive at every
such place, including the zero and pole charts.

At a good prime where a_h vanishes, [h]P reduces to a
2-torsion point T, including possibly O. Translate it
to the formal group by the actual torsion representative.
The chart is, up to the known sign at T, a unit times the
formal uniformizer. Since m is even, [i]P reduces to O, and
formal multiplication by m cannot lower the depth. Thus
a_h divides a_i at every good place. This is a statement
in the localization away from 2 and 7, not an assertion
that the complete global integer quotient has no bad
denominators. Likewise b_h and b_i are coprime at each
good place: a pole is an exact order-four class with
double (0,0), and multiplication by even m maps it
to 2-torsion or O, never another pole.

It follows also that U_i/U_h has primitive good-place
denominator b_i: write it as b_h(a_i/a_h)/b_i, and when
b_i vanishes, a_h,b_h,a_i are all units. The one
good-place exact division a_i/a_h can be computed
with a finite precision guard. If v(a_h)=r is
certified by a nonzero normalized leading digit,
work mod p^(k+r) in the unramified local component
to get the quotient mod p^k, after division of
both coefficients by p^r and inversion of the remaining
unit. At split primes use the two Hensel components
separately if the depths differ. This procedure
never treats an original 0/0 as a modular inverse.

## A raw integer formula with no exact divisions in its SLP

Write N_f for field norm from Q(√2). Define the exact
integer quantities

    U=N_f(b_h), V=N_f(b_i), P0=N_f(R b_h²+a_h²),
    S_h=N_f(a_h), S_i=N_f(a_i).

The source definitions give N=P0/(R² U²) and
Q=U S_i/(R¹⁵ V S_h), so the exact c is M/D0, where

    M  = 12 (R²⁵ P0² V² S_h² + U⁶ S_i²),
    D0 = (1+A) R²⁹ U⁴ V² S_h² > 0.

In particular this is a division-free finite SLP in
integer arithmetic. No sign is lost by squaring the
appropriate source terms. It gives raw c, not already
reduced C and Z.

For modular evaluation, keep the normalized polynomials
q_n=ψ_n for odd n and q_n=ψ_n/(2y(P)) for even n,
with their usual finite starting values. The standard
recurrences give q_(2j) from q_(j−2),...,q_(j+2)
without division; for q_(2j+1) exactly one of the two
terms acquires the explicit factor (2y(P))⁴ depending
on the parity of j. Thus a rolling window with fixed
radius 6 around each binary prefix of n suffices:
for next prefix 2a+b, children of its offset r
have old offsets floor((b+r)/2)+u, |u|≤2.
All indices stay within the old window.
This uses O(log n) ring operations and a constant-size
window of ring values aside from the input exponent
bits, even for the literal 104414-bit i. It neither
requires a reduction period for the division polynomials
nor assumes that such a period equals the point order.

The deterministic replay uses no point-period shortcut.
It checks signed primitive chart coordinates against
affine addition on three inert primes and six split
components, including 39 nonzero pole cases, and evaluates
the full actual 104414-bit i at two known prime-square
rows. It recovers c≡5134 mod 83² and c≡1495 mod 131².
The latter reruns the exact truncated cancellation
v_131(a_h)=2 instead of treating a vanished residue
as a denominator. It also gives δ≡10742=82·131 mod
131², with no assertion about reduced H mod 131².
These controls certify the raw recurrence, not a
new reduced-Z phase.

## Precisely where the global odd denominator lives

Away from the fixed bad/normalizing primes, put
T=N_f(a_i/a_h). The nuisance factor S_h can then be
cancelled before the outer addition, giving

    W = (R²⁵ P0² V² + U⁶ T²)/(R²⁹ U⁴ V²).

At a good prime outside R(1+A), set
a=v(U), b=v(V), u=v(P0), t=v(T); these are nonnegative.
The squared summands have depths 2(u+b) and
2(3a+t), and the denominator has depth 4a+2b.
An odd reduced denominator requires equal summand
depths followed by odd cancellation before reaching
that denominator depth. If a=0, the first summand
already has depth ≥2b, so any equality is too deep.
If b=0, the second summand has depth ≥6a, likewise
too deep. Therefore both a,b must be positive.
Same-place coprimality of b_h,b_i forces this common
support to be split in √2 with opposite prime
orientations, exactly the good split support of the
oriented ideal (b_h, conjugate(b_i)).

This is an explicit source arithmetic description
of the odd normalization support, stronger than
including all primes of either gigantic raw chart
denominator. It does not compute its parity. In
particular ordinary modular residues of M,D0 modulo
an unrelated test prime do not certify the global
common factor or its phase. The raw denominator
contains genuine even powers near many primes, and
replacing it by the reduced representative there
without the global cancellation loses the distinction.

## Normalized all-place proof certificate directly on the raw SLP

One can test a claimed positive τ without factoring
M,D0 or expanding a separately proposed H,C0,L0
if given the following exact arithmetic witnesses.
Let g>0 be certified to be gcd(M,D0) by g|M,D0 and
a Bezout equality uM+vD0=g. Put

    H_raw=D0²−βM²,       L_raw=48D0²−49βM².

Then support is tested by B_*|β, g² H_*|H_raw, and
τ=B_* H_*>0, with the same 131 normalization.
The fixed rows use the actual unit D0/g modulo their
primes, which can be authenticated by exact division
or by a prime-power precision certificate for g,D0.
There is no requirement that H_* itself be squarefree.

The factor-free moving rows of c2cd6e57 become the
following literal weighted checks in raw inputs:

    M | 12g(a_C²+3β b_C²) − 12τ D0
    M | 24g a_C b_C
    L_raw | 96g²(a_L²−b_L²) − 672τ g D0
    L_raw | 192g² a_L b_L
    gcd(96g² a_L,L_raw) = 96g² s².

They are exactly the normalized modular witnesses
after multiplying by 12g and 96g² respectively
(C0=M/(12g), L0=L_raw/(96g²)). No prime enumeration
or squarefree factorization is used. Each divisibility
or gcd in a formal certificate can itself be supplied
as exact quotient/Bézout identities on those same
raw SLP outputs. This is a verification interface;
a factored representation is not needed, but exact
identities are. A handful of modular checks of these
huge equalities does not prove them.

No compact producer of g (or even the required
oriented odd phase), divisors, and modular roots
is currently established for this exact h/J.
The recurrence does not make expanded coordinate
arithmetic practical, and no complexity-theoretic
impossibility is claimed. The verified improvement
is a raw modular source and a proof-level normalization
and τ interface, not an actual all-place or global
solution for a new parameter.
