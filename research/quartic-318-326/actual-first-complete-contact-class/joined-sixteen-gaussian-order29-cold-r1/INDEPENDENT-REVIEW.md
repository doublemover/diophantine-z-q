# Independent review: Gaussian order 29 and sixteen literal contacts

Bound to exact author note
1e1266bab8bf95b7f027361d133c281a2464bbad673f3755f4323b30509fb2b5,
manifest a8aa780391cb71f9c0d054dd0e36d393801dc02f58a4cfbb9a431ea268b7363a,
and exact JSON 6e0f43b016f3ae9e599658f7a96e08afd36bde693ab2b6053357e63a102d07a1.

I independently calculated the signed Gaussian multiple on the
original E first and only then applied the actual 2-isogeny
X=x−(3−sqrt(2))²/x. The exact coefficient denominator is the
square of 996479897881955092985794918173310653967408040161,
with the eight displayed prime factors verified by trial division.
For p=1 mod 8, the basis-to-four-embeddings matrix has unit
determinant; denominator divisibility is equivalent to a pole
at one of those actual places. For p not 1 mod 29, the rational
29-torsion has dimension at most one by Weil pairing and I
acts on the nonzero line by a square root of −1. Thus it is
enough to calculate both signed Gaussian multipliers (their
denominators agree by i-conjugation). In the reverse direction
a pole implies [29] kills the reduced P, and P is an actual
finite point, hence not O. This does not exhaust nonsplit
primes or primes equal to 1 mod 29.

Recomputed both original R orders and midpoints in each of
the six above-threshold candidate rows. Exact weak-CRT shortlist:
415721, 6469193, 9807649. The first and last have original
opposite full order 29, rather than just order modulo T0.
Separate exact lifted affine/formal arithmetic gives the
actual first returns, four original Lucas charts, p-unit
coefficients, three scales and all twelve distinct root
residues at each selected prime. The new simple contacts
are slot 241 at θ=−32/407 and slot 292 at θ=1/2399.
No old Gaussian p=1 mod 408 assumption is needed for the
pointwise argument. Independently checked that the new
literal h and numerator congruences keep every earlier
condition, with the same least positive CRT h and old
finite scalar guards/labels, not the same exact old scalar.
Directed right-to-left Decimal interval arithmetic puts the
actual rational norm inside
[−1059640787916845915,−1059640787916845914]/2^64
at that index, hence outside [−1/100,1/100].

At the two new primes the previously verified pointwise
sixteen-leaf fold applies to give v_p(b_j)=1. These and
the preserved fourteen incidences are exact local rows
on the common symbolic saturated positive-square branch.
The d=204 numerical row is just a residue replay. Each
newly hit class still has a 7-nonsquare defect; the four
other hit classes retain their independent defects, and
the remaining six unhit classes retain separate unit
nonsquares. Thus 16+6+6=28 distinct odd-support primes
are necessary on that same branch. This proves neither
a complete actual support nor order-compatible new primes,
square pole denominators, a rational PointPair, or Lean.

Replay takes the exact JSONs for prefix, singleton,
triad, six, XII, XIV, XVI (in that order), verifying
all seven SHA-256 hashes directly. Standard Python only.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
