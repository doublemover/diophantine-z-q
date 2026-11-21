# An exact finite rejection at the original fixed-h slot 190

Keep the exact a=0 retuned h,J, explicit odd Lucas labels, fixed scale,
pre-pole source assignment and same scalar as in the independently
checked prefix a7dd144b…. This works with the actual unscaled detector
at slot190. It rejects a new precisely specified family of common
contact inputs t for that fixed h. No other h or nonlisted t is
ruled out, and no PointPair is claimed.

## A concrete t family that passes the prefix and the small places

Form a positive integer B_bad whose prime divisors are exactly the
optional escape set below together with all exceptional primes for
the unscaled detector in dd5d6ca1… and 7630bf5f…. It can be taken as
the product of the exact nonzero numerator and denominator of w37
in reduced form, denominators of all 32 coordinates of the exact
16 fixed detector coefficients, and the fixed constants

    2·3·5·7·17·2399·407·2398·439.

The last factors cover all contact coefficient denominators,
the numerator support of F(1), all leading-coefficient support
and all pair determinants; repeat primes cause no issue.
Multiply additionally by all nominated optional primes if not
already present. This is a literal integer circuit at the
fixed source w. Neither factorization of the integer nor
expansion of the huge label coordinates is assumed. For the
following explicit recipes the optional finite set S_free is
known numerically. With the composition of exact division
operations define

    B_sat = B_bad / ∏_{p∈S_free} p^{v_p(B_bad)},       D=B_sat^m,
    R=N D+1,                                             t=(R/D)^2.

The letter R here denotes only the contact numerator root.
Its exact coprimality to D makes rational t have reduced
square denominator. Take m≥12 and large enough for the nine
finite small-prime inequalities of a7dd144b…. Since D has
v_p(D)≥m for p=2,3,17, the same proof works, with exact
valuation 2v_p(D)−12v_p(c_j)−2v_p(2) on each detector.
Take N large enough for the explicit archimedean bound there.
For example make N larger than D and the ceiling of every
positive bound displayed in that proof. This selects one
single exact positive t (or a whole family as N varies).
It completes the **pre-pole** rows and gives positive <17
and the exact local small-prime conditions at all three
literal poles, while the same scalar and anchor are unchanged.
These descriptions are symbolic exact arithmetic, not
specific expanded integers or an all-place Ready verdict.

At slot 190 put u=R²,v=D². Its exact five contact numerators
are

    G0=u, G1=2u+v, G2=u+v, G3=2399u−v, G4=407u+32v.

They are positive for the chosen real t. Out of the prime
support S of B_bad, any positive valuation of one G_j is
that of F(t) (primitive pair plus unit pairwise determinants);
dd5d6ca1… proves it MUST be even if the slot has a PointPair.
For p∈S∖S_free, D is p-adically deep and R a unit, so the exact
valuation of G_j at p is the valuation of its leading
coefficient a_j. The inequality 2v_p(D)>v_p(a_j) is even
automatic from m≥12 and the literal a_j. These are genuine
conditions on the actual t above, not an arbitrary genus-five
twist tuple picked independently of the detector.

## Strong direct rejection allowing fifteen specified escape primes

One can leave **all** the following primes outside D:

    S_free={7,11,13,37,53,109,131,163,439,661,733,1489,1861,2399,1041427}.

Use the unchanged formula above for D. In particular 5 remains
saturated. Suppose the actual coefficient in slot190 has a
PointPair. Consider G4 alone. Its only leading prime factors
are 11 and 37, both unsaturated. At either of these p,
G4≡32D² is a unit, so **neither** factor can occur in its
squarefree part. This is why the baseline for G4 here is 1
rather than 407. At any other p∈S_free that can occur in its
squarefree part, necessarily

    (−32·407/p)=+1

by the genuine equation R²/D²=−32/407 modulo p. Apart from
11,37 the only eligible primes in the displayed set are
163,439,661,733,1489,1861,1041427. **Every one is 1 mod3**.
At all saturated primes the squarefree contribution is
trivial, since none divides 407, and the outside-S parity
excludes every other contribution. Hence the positive
squarefree part of G4 would be 1 mod3. In fact G4 is a unit
at 3 with G4≡407R²≡2 mod3. Contradiction.

This is an unconditional rejection for that explicitly
specified family at the actual fixed h. It only needs the
one-form root residues and 3-unit check, not an assumption
on rank, the factorization of B_bad, or factor discovery at
the prime that eventually obstructs. Prime 5 cannot simply
be added to the escape set: it has the required root and
is 2 mod3. Unsaturating other genuinely eligible 2 mod3
coefficient primes also evades this particular obstruction.
Those are precise choices a next search could explore.

The adjacent finite checker also restricts a sublist of eleven
free primes (omit 7,439,1489,2399) on the **first three**
forms, independently from this fourth-form rejection.
Their baselines really remain 2,1,2399 in that sublist.
Each extra squarefree factor d_i must be 1 mod24 and a
square at 17. At p|d_i an allowed root requires
(-a_i b_i/p)=+1, and each other form has unit symbol
(a_i det_ij/p) because D is a unit there and
G_j/D²=det_ij/a_i at that root. All determinants are units
on this sublist. The exact finite rows are 4,16,4 allowed
single masks, seven two-form pairs, and only the all-trivial
triple once the third form is imposed. This is a separate
effective screen, not an incorrect fourth-form baseline.

## The minimal forced tuple and an exact rank-zero genus-one check

If S_free is empty, the same construction forces the
actual tuple of squareclasses (1,2,1,2399,407) at the
five squared-denominator contact numerators. Already
G1 and G2 require

    A²=R²+D²/2,     C²=R²+D².

With R,D positive this would give the half-scaled area
D²/2 from the right triangle legs C−R,C+R, hypotenuse 2A.
Scaling its lengths by 2/D would give area 2. Thus the
genus-one test on this square-t chart is the classical
congruent-number E₂: y²=x³−4x. Explicitly for a right
triangle lengths a,b,c and area n use
x=n(a+c)/b, y=2n²(a+c)/b²; elementary substitution gives
the equation and a nonzero ordinate.

Here no tabulated rank is needed. The literal rational
x-class images in the two-isogeny descent have sizes 4 and 1:
E₂ has B=−4, only possible classes ±1,±2, all supplied
by its rational 2-torsion. The dual has y²=x³+16x, so
negative classes cannot occur over the reals and the only
nontrivial possible class is 2. Its primitive quartic
N²=2M⁴+8e⁴ is impossible: the right side has 2-adic valuation
1 for odd M and 3 for even M and odd e. Therefore the
ordinary isogeny index formula yields rank zero (see
[Cremona §2.2](https://johncremona.github.io/papers/d2.pdf)
for the signed x-class and quartic conventions).
Good reduction at 3 and 5 gives exactly four points
at each, so rational torsion is just E₂[2]. This
rules out area 2 without any analytic rank or Sha
assumption. More simply, for the explicit choice
N>D made above, (R²<G_1/2<(R+1)²); so at that
concrete t a new odd-exponent factor outside S is forced
even without descending an elliptic curve. The E₂ test
excludes the same minimal tuple for *any* positive R,D,
without relying on this height gap.

**Scope:** one fixed retuned original h and fixed scalar,
with one common t given by an actionable exact construction
and a proof why that construction cannot complete slot190.
It does not exclude other choices of t, or the mixed CRT
selection that chooses h after seeing actual contact support.
It is useful to distinguish practical escape primes from
the much larger collection irrelevant to G4 and from the
all-saturated rank-zero tuple. No full support enumeration
or original rational points are claimed.

```sh
python3 -B check_contact_escape.py | cmp - EXACT-FINITE-CONTACT-ESCAPE-CONTROLS.json
sha256sum -c SHA256SUMS
```
