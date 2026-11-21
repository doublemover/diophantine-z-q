# Pythagorean square contact: exact local obstruction and generic limit

Keep the literal unscaled detector slot190 and its actual guarded
integer h, labels and nonzero input b. Work at primitive r,d>0
with t=(r/d)^2>2. Try the natural extra condition

    r²+d²=s².

This removes the odd support of the original contact G2 and also
makes all odd divisors of G1 *split* in Q(sqrt(2)). Nevertheless a
PointPair for the original pole in this family **requires 407|d**.
In particular the standard d supported only at 2,3,17 cannot work
with this extra condition, regardless of the original h or its
depth. Including 407 in d cures these two local obstructions but
does not automatically settle G3 or G4. The natural family does
not supply a generically valid joint norm representation of them.

## Literal factors and the first two supports

Write u=r²,v=d² and

    (G0,G1,G2,G3,G4) =
    (u, 2u+v, u+v, 2399u−v, 407u+32v).
    F(t) = G0 G1 G2 G3 G4 / (2·2399·407·d^10).

G0 and G2 are squares. If an odd p divides G1, r and d are units
there by primitivity, so −2 is square modulo p. Since
G1=r²+s² as well, −1 is square modulo p. Thus 2 is square;
this proves the assertion at all its odd divisors, not just
those of odd multiplicity. It does not certify the needed
elliptic orientation of these split divisors.

## Both denominator primes must be saturated

Suppose d is a unit at p=11 or p=37. Then T=u/v is a residue
square with T+1 also square (including zero). The full finite
row replay shows:

- At 11, none of G1,G2,G3,G4 can vanish on these simultaneous
  square residues. In particular G1's only root T=5 makes
  T+1=6 nonsquare, and G3's T=1 makes T+1=2 nonsquare.
- At 37, the only possible vanishing among those four is G2
  at T=−1. Its valuation is even by the very Pythagorean
  requirement. G4 is a unit in both rows as its linear
  coefficient vanishes but 32 is a unit.

G0 contributes an even valuation; the denominator has valuation
one, so e=v_p(F(t)) is odd in either row. For e>0, one must have
T=0 or T=−1, hence Delta=t−1 is a unit. The prime is inert in
Q(sqrt(2)) (both 11 and 37), so the exact early-eight proof
63be7c0a excludes this contact for a PointPair, whatever h is.

The other case e<0 is not an application of that positive-odd
theorem. Here T is integral at p, so d_Delta=v_p(t−1)>=0.
The actual weights w151,w156,w158 have valuations

    2 d_Delta−e, 32 d_Delta−7e, 122 d_Delta−25e,

all odd. The sixteen actual coefficients have even or infinite
valuation by the original coefficient-parity lemma (2 and 49
units). Starting from 1, the parity-minimum fold gives final
valuation at most zero at both conjugates, without assuming
the coefficients integral. The reciprocal trace has nonnegative
valuation if nonzero and the trace quotient has nonpositive
valuation. In the zero case the literal total-division pole is
zero, excluded. Otherwise the pole has valuation
e+2v(traceQuotient)−6d_Delta<0 of odd parity, which contradicts
the exact PointPair denominator obstruction dd5d6ca1.
Consequently each of 11 and 37 divides d.

Conversely, imposing p|d for either of these sites makes r a
unit, G1,G2,G3 units, and G4 have exact valuation one.
It cancels the denominator's one valuation, leaving only
v_p(F(t))=−10 v_p(d), even. This does not interfere with the
two-form norm argument or the existing 2/3/17 depth prescriptions.

## No generic joint norm identity after Pythagorean parametrization

Use the primitive Pythagorean parametrization
r=m²−n²,d=2mn,s=m²+n² (for rational representations, common
scalings make no difference to the quartic valuations below).
At x=m/n the remaining two homogeneous polynomials, dehomogenized,
are

    H3(x)=2399x^4−4802x²+2399,
    H4(x)=407x^4−686x²+407.

Both are irreducible over K=Q(sqrt(2)). Indeed a monic even
reciprocal quartic x^4+B x²+1 could only factor into two
quadratics of the form (x²+a x+b)(x²−a x+d), bd=1, with
a(d−b)=0. A linear root is also a possible quadratic pair
because its nonzero negative is another root. If a=0 the
discriminant B²−4 must be square; otherwise b=d=±1 and
±2−B must be square. The rational quadratic classes of these
three candidates are respectively

    H3: 6, 6·2399, 2399;
    H4: −30, 15·407, −2·407.

None is a square or twice a rational square, the exact two
ways a rational can be square in K. The checker verifies the
class quotients and the nonsquare conditions by exact fractions.

Thus H3 and H4 are distinct degree-four polynomial places in
Q(x) remaining irreducible over K. Each has even valuation
in any norm from K(x), since its conjugate irreducible is
itself and valuation of y times conjugate(y) doubles. Their
product has odd valuation at both. No multiplying by nonzero
constants, squares, or a common homogeneous scale can give
a generic norm identity for H3 H4. This also rules out the
same simplification for the full original F on this generic
Pythagorean family: G0,G2 and the denominator d^10 are squares,
and H3,H4 are coprime to the remaining G1 polynomial and to
the finite constants. Saturating d at 407 is a condition on
numeric parameters; it does not change this rational-function
norm obstruction.

The generic statement does **not** exclude every rational
specialization. A specialization can have even valuations at
all inert places despite no function-field norm identity.

## Exact saturated test and remaining scope

The direct parameter choice (m,n)=(41514,1) gives
(r,d,s)=(1723412195,83028,1723412197), with d divisible by
2,3,17,407 and t>2. Here the actual inert p=35533 divides
G4 to exact exponent one and is a unit for all other contact
numerators, d and Delta. The five modulo p² rows and
primality and nonsquare tests all replay exactly; no complete
factorization is invoked. Early-eight again excludes a
PointPair at this particular numeric t for all guarded h.

Hence d saturation is necessary but not sufficient, and forcing
the first two easy representations leaves a genuine arithmetic
condition at H3,H4. This result concerns the literal unscaled
slot, not a constructed common square support for all three
detectors, not failure of every d containing 407, and not a claim
about all t or Lean.

    python3 -B check_pythagorean_contact.py | cmp - EXACT-PYTHAGOREAN-CONTACT.json
    sha256sum -c SHA256SUMS
