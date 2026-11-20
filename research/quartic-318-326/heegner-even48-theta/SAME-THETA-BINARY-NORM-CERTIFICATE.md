# Exact support certification by one binary norm

Keep the actual scalar W=w/e, a=0 or −1, and corresponding H
defined in MINIMUM-SCALAR-GENUS-COMPATIBILITY.md. In particular
1−b/17=H/((1+A)e)^2 with positive odd squarefree part θ.
Do not replace W by 1.

Let m be a positive prime ≡23 mod24, m∤θ, and K=Q(√−m).
Then every θ-prime splits in K if and only if there exist
integers X,Y,Z with Z≠0 and

    X²+mY²=H Z².

In the forward direction the rational norm class of H equals
that of θ. Each odd unramified nonsplit prime has even
valuation of θ (zero), and unramified local norm maps are
surjective on units; at split primes there is no restriction.
The prime 2 is split since −m≡1 mod8; at infinity use θ>0.
At the ramified prime m, reciprocity makes
(θ/m)=∏_(q|θ)(−m/q)=1 and θ is a local square unit.
This gives all local norms, so Hasse–Minkowski for the
diagonal three-variable conic gives a rational norm pair
and clearing denominators proves the equation.
Conversely at every inert odd prime a norm has even
valuation (degree-two residue extension), so every
q|θ must split, using m∤θ and θ odd. This implication
alone works for a composite squarefree m under the same
coprimality assumptions. A compact certificate can thus
be directly verified by integer arithmetic without
factoring H; no practical cost guarantee is asserted for
finding X,Y,Z for the actual unknown H.

As an exact demonstration of certificate format only, the
baseline F=250907860680726875559825159650206985141521 is a
norm class for m=450071, with literal integer solution

    (X,Y,Z)=(1312177335665825927737805,2863126577452331885881,4644).

Multiplication verifies it. This certifies the complete F
support, never the actual H unless the actual ratio H/F
is separately known to be a norm. For composite m=14231,
θ=241 is a split prime, θ≡1 mod24, yet the ramified
local signs at (7,19,107) are (−1,−1,+1), so θ is not
a norm. The product Jacobi symbol is insufficient there.

## Why the scalar norm and any finite CRT list do not settle it

Write U=A/17, T=1+A. The original extraction makes β
the squarefree part of U, and 1−b/17=1−U(W/T)^2 a norm
from the real field Q(√β). This explains why every θ-prime
prime to β splits in that real field, but does not
give a norm from an imaginary field.

More precisely, allowing rational N,Q subject just to
W=N²+RQ², the old finite nonempty local and strict real
open conditions do not force full support splitting in
*any fixed* imaginary K whose discriminant is prime to
the extra prime chosen below. Pick q outside all specified
places and 2·R·U·T, split in Q(√β) and inert in K, by
Chebotarev for the compositum of the distinct quadratic
fields. The unit equation U·W²≡T² mod q has a simple
root. Exactly one lift of each such root modulo q² remains
a root mod q²; taking another lift makes q appear to
valuation exactly one in 1−U(W/T)^2. The local map
(N,Q)↦N²+RQ² is the norm of a split/unramified quadratic
étale algebra at q and surjects units of ℤ/q²ℤ, so it
attains the chosen class of W. Weak approximation for the
two rational coordinates attains this and keeps the prior
open conditions at the other finitely many places,
including the real positivity/smallness domain. Now q is
an inert odd divisor of the resulting θ. This is a genuine
barrier to reasoning only from finite CRT plus the scalar
norm identity; it makes **no** counterexample within the
singular actual h→(N,Q) producer, whose additional rigid
image could impose a new identity not proven here.

No central value or rank statement follows merely from
passing the binary norm test. If m remains genuinely free
after the whole θ is fixed, the earlier CRT result gives
an admissible prime m even without factoring H to choose
it; auxiliary analytic nonvanishing is separately required.
