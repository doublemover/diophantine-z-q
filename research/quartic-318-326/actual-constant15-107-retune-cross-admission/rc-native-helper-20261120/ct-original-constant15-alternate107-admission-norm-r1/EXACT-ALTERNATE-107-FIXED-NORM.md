# Exact joint admission of the alternate 107 lift by one fixed norm

Keep the genuine retuned original scalar with v₁₀₇(δ)=1
and stripped δ/107=1. In particular the exact old scalar
input a=0, h, and the seven old local rows stay fixed.
Write θ=[δ], d=βθ, T'=107·131·6551·2470991·16782959
and e=2952271997968816765. The old named lift and old
opposite class e were both rejected on this specialization.
We consider instead:

1. the alternate full 2-Kummer lift (θ,θe,e) of the same
   marked scalar θ on E′_d;
2. the exact new opposite class
   f=65029284442765=5·17·107·733·1489·6551 in Selψ.

Set a=e/5=590454399593763353 and F₂=Q(√a,√f). The
two new admissions hold **exactly** when the following
one fixed equation has a rational solution:

    N_F₂/Q(η) = 937 δ/T'.

In the basis 1,√a,√f,√(af) the left side is

    (x²+a y²−f z²−a f w²)² − 4a(x y−f z w)².

This requires neither a hidden-prime count nor an expanded
factorization to verify a supplied norm. No solution to this
new norm equation is asserted.

## 1. Both conditions at every place

The literal isogeny E_d→E′_d has x-coordinate
X=x+41d+400d²/x. For any nonexceptional point,
X−d=(x+20d)²/x and X−81d=(x−20d)²/x.
Thus the full Kummer image of the φ-kernel of the
first scalar projection is (1,g,g) for g in the
opposite scalar image on E_d. The formula extends
to the finitely many exceptional points by local
continuity. This describes how to change the last
two coordinates of a fixed first Kummer class.

At odd p|θ, β is square, so the local point
T'_{81d} has ordered Kummer tuple (θ,5θ,5).
The desired tuple (θ,θe,e) is available exactly
when 5e belongs to the local opposite image {1,−d}.
At an old visible θ prime (5/p)=+ and e meets the
old opposite place condition, so this holds.
At 107, both 5 and e are nonsquare units, so 5e is
already a square. At each *further* prime q|θ,
5e is a unit and must be square; this is (a/q)=+,
since 5e=25a.

At β, θ is square and e obeys the old local
opposite conditions, so the alternate tuple is
available from the identity class. The same works
at 2,3 and infinity. At all other odd primes not
dividing d the E′ model has good reduction, and
all triples of unit classes with product one are
its local full Kummer image: this subgroup has
size four from reduction and full rational E′[2],
and all coordinates of every point are units
modulo squares there. The stated tuple is such a
unit tuple. This proves the exact criterion for
the first admission.

For f, use the same true stripped d-unit bits at
each of the thirteen known odd places. The replay
verifies directly, with no assumption on other support,
that f has the required class (−d)^v_p(f) there.
At 3 f≡1 mod3, at 2 f is an odd unit, and at infinity
f is allowed; other good odd places admit all unit
classes. Thus its only extra tests are (f/q)=+ at
every further q|θ.

## 2. The correction and the full group at 5

Put U'=θ/T'. This is positive, odd, and is coprime
to both radicands. The true stripped d-unit data give
(U'/p)=− exactly at p=5,11,1489 among all primes
ramified in either of the two quadratic fields.
The positive prime 937≡1 mod24 realizes precisely
these signs. Of those primes, 11 and 1489 divide a,
while 5 and 1489 divide f. Quadratic reciprocity
therefore certifies that 937 splits in both fields.
It may incidentally divide U', which does not alter
the criterion since it splits.

The local solution test for N=937 U' is now exactly
that both quadratic Hilbert symbols (a,N)_v,(f,N)_v
be +1. Indeed at the fixed odd ramified places the
correction makes N a square unit. At 2, a≡1 mod8
while f≡5 mod8 and N is a unit; at infinity both
fields split. At any other odd prime the test is
neutral on units and, when that prime divides U',
is precisely the two required Legendre signs.
Local reciprocity identifies the norm subgroup
of the biquadratic algebra with the intersection
of the two quadratic norm subgroups.

At 5 the defining squareclasses are independent:
a≡3 mod5 is a nonsquare unit, while f has valuation
one. Thus that decomposition group is all V4 and
Tate's restriction kernel in H³ is zero. The Hasse norm
principle applies, as in [Frei–Loughran–Newton, Theorem 6.1](https://pure.manchester.ac.uk/ws/portalfiles/portal/55657924/HNP.pdf).
Finally δ/T' differs from U' by a rational square,
which is itself a local norm everywhere and hence
a global norm in this field. This proves the
equivalence exactly with the folded rational δ.

If there is exactly one further θ prime past 107,
it passes both conditions by the earlier aggregate
characters and exact scalar matrices, so the norm
exists in that conditional case. A certificate may
also exist with more further primes; there is no
count assertion. The alternate crossed pairing
against the same f is a separate computation.
This equivalence does not supply a rational norm
coordinate, marked point, or rank.

    sha256sum -c SHA256SUMS
    python3 -B replay_alternate_norm.py | cmp - EXACT-ALTERNATE-NORM-CONTROLS.json
