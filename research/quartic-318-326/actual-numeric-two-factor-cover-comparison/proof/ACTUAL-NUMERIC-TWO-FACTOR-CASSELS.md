# Two numerical same-scale genus-one covers: a Cassels obstruction and a one-line radical

Keep historical \(p_a=415721\), the exact original scalar \(J\) and sixteen
indexed contact \(w\bmod p^2\) balls, the same three actual reciprocal
scales \(c_0,c_1,c_2\), and the original phase-period index \(h\). Each of the
following numerical instances has its own single simultaneous \(h\) extending
the very same archived XVI condition. The chart variable is \(W=c_1w\).
Neither instance satisfies all the old auxiliary \(B\)-saturation conditions.

## Numerical support and exact original cells

Write \(s=-32/407\), \(t=1/2399\), \(\delta=t-s\), and use the original
negative and positive root factors on the **same** middle-scale variable:
\[
 C_{a,b}:\quad W^2-s Z^2=a U_0^2,\qquad W^2-t Z^2=b V_0^2.
\]
The shared negative support is \(a=415721\cdot 163199081=67845285152401\).
The two genuine positive supports and twists are:

| instance | \(q_1,q_2\) of \(b\) | \(D=ab\) |
|---|---|---|
| A | 7497601, 25515769 | 12979281709686225818153925769 |
| B | 16990081, 17238721 | 19871020087852834114214638801 |

All six distinct supported primes in the two experiments
are used only after exact trial-division primality checks (the shared
historical \(p_a\) is already a certified prime of XVI). Each new row is
split, \(1\bmod8\), prime to the old order modulus and exceeds 76176. The
actual lifted Gaussian generators and arm data are:

| p | Re/Im of Gaussian generator | selected \(\sqrt2\) | orders \(o_+,o_-\) |
|---:|---:|---:|---:|
| 163199081 | 11941, 4540 | 10317486 | 2039690, 40805741 |
| 7497601 | 2399, 1320 | 1562975 | 31260, 15481 |
| 25515769 | 5037, 380 | 2021933 | 1594106, 6381461 |
| 16990081 | 2209, 3480 | 13934422 | 849725, 29489 |
| 17238721 | 1761, 3760 | 1445536 | 107720, 4310561 |

For each instance the group counts \(p+1\pm 2\Re\pi\) are arithmetically
checked, of odd gcd 1, and prime to the other mover support and all old
contact primes. The actual orders above and their first formal returns
(depth one) are checked by weighted Jacobian arithmetic lifted to \(p^2\).
The new CRT keeps all archived \(h\)-congruences and the exact
\(h=0\bmod o_+,h=1\bmod o_-,h=p^3\bmod p^4\) for every new point.
The two least positive common CRT representatives have 2789 and 2783
bits, respectively; exact dyadic intervals for their original real chart
norms have numerators \((-799829712713654886,-799829712713654885)\)
and \((-2773468287805467621,-2773468287805467620)\), divided by \(2^{64}\).
Both pass the same \(1/100\) real index guard.

At the new negative prime use \(W^2=s+a\) modulo \(p^2\), and at the
new positive primes use \(W^2=t+b\) modulo \(p^2\). The actual \(c_1\)
values and signed label-order reductions are recomputed, so the given
\(W\) lifts to the intended \(w\) by a unit division at each place. The
other factor is a square unit after dividing by its multiplier. In both
instances the exact first-return checks and the twelve distinct
nonzero chart roots ensure a single simple negative/positive middle
contact at each respective new prime; all \(1-c_j^2w^2\) and both
other full factor rows are units there. At each of the sixteen older
places the replay tests the exact preserved residue \(W=c_1w\bmod p^2\)
and verifies both quotients are square units. This includes \(p_a\) as
a depth-one negative contact with exactly the originally reserved
\(w\)-residue, not the all-fresh replacement ball.

For all-local solubility it remains to handle the actual fixed bad places
\(2,3,5,7,11,37,2399\), infinity, and good odd places outside \(D\).
Both \(a,b\) are square units at all seven fixed bad places, so a
sufficiently negative \(W\)-valuation produces both squares there
(\(Z=1\)); at infinity take \(W>2\). At every unspecified good odd place
the diagonal quadrics reduce to a smooth degree-four complete
intersection: all diagonal coefficients and \(s,t,t-s\) are units.
Indeed their pencil has four distinct singular members, or one can check
gradient rank directly. Its genus is one, and the Hasse bound yields
a finite-field point which lifts by smoothness. These arguments give
local points over every completion, not simultaneous rational \(W\).

## Exact full Selmer rows and exact arithmetic pairing

The marked \(2\)-cover of \(E_D:y^2=x(x-Ds)(x-Dt)\) is the above curve
via \(x=D W^2/Z^2,\ y=D^2 WU_0V_0/Z^3\). The raw Kummer triple, in
root order \((0,Ds,Dt)\), is \(\alpha=(D,b,a)\).
Use square scaling by \((407\cdot2399)^2\) in the split
Kummer images and the verified fixed small-place rules of the
same-scale construction. At both movers of \(a\) its local
root signs are \((s,t,\delta)=(+,+,-)\), and at both movers of \(b\)
they are \((-,+,+)\). The two within-pair signs are +; the
ordered \(q_1,q_2\) cross columns over \(p_a,q_a\) are
\((-,-),(+,+)\). The script verifies the actual torsion quotient
tables at all four movers and at the fixed 11,37,2399 directly on
the scaled numerical roots. Normalization by triviality at \(q_2\)
kills exactly the rational \(E[2]\) plane, since the four local
torsion images there have distinct valuation vectors; the raw
\(\alpha\) is normalized by torsion at the root \(Dt\).
An exhaustive numerical finite Kummer calculation yields exactly the
eight-class normalized Selmer group in each instance, with basis
\[
 F=(2399,\ 7\cdot11\cdot37\cdot2399\,a,\ 7\cdot11\cdot37\,a),\ \
 U=(2399a q_1,\ 2399q_1,\ a),\ \
 V=(11,\ 5\cdot2399,\ 5\cdot11\cdot2399).
\]
These are positive rational squareclasses, and \(F\) is precisely the
raw mark's normalized representative. There is no numerical prime
selection by Chebotarev or inference of a pairing sign from a
quadratic phase.

For ordinary Cassels pairing take
[Shukla–Stoll §3.2, (3.9)–(3.10)](https://arxiv.org/pdf/2302.01640)
on the exact split curve. For any first triple \(d\), with roots
\(e=(0,Ds,Dt)\), its \(i\)-th conic has equation
\(d_j z_j^2-d_k z_k^2+(e_j-e_k)z_3^2=0\), where \(j,k\ne i\).
The data gives three verified primitive integer tangent points
for each first triple. If \(Q_i\) is such a point and the integral
conic coefficients are \((l_j,l_k,l_3)\), its tangent is the
polar form \(l_j Q_{i,j}z_j+l_k Q_{i,k}z_k+l_3Q_{i,3}z_3\).
The true ordinary pairing is the product of its three Hilbert
symbols with the second triple over all completions. Rational
global rescaling of a tangent does not change the total product.
The certificates use \(\alpha\) or \(U\) in the first slot; the
rational torsion difference between \(\alpha\) and \(F\) pairs to zero.

The independent-of-search verifier uses **only standard Python**.
For each local row it checks Hensel's quadratic inequality on each
reported rational approximate root and computes the guaranteed
precision of each linear tangent evaluation, even at 2. It then
recomputes the exact Hilbert symbols from valuation and unit parts.
Square-second-argument places can be omitted immediately. At infinity
every second argument is positive. All remaining odd primes not listed
are good, larger than 29, and all coefficients are units. Reduce the
three nonzero tangent hyperplanes and the infinity hyperplane; each
meets the smooth nondegenerate degree-four curve in at most four points.
The Hasse lower bound is strictly larger than 16 for all those odd
primes, so choose and lift a point avoiding all four. The tangent
and second argument are units there, hence Hilbert product is +.
This also accounts for any uncontrolled primes dividing particular
coordinates of the chosen tangent points, which are primitive.

| instance | \((F,U)\) | \((F,V)\) | \((U,V)\) |
|---|---:|---:|---:|
| A | \(-\) | \(-\) | \(-\) |
| B | \(+\) | \(+\) | \(-\) |

For instance A, the first nontrivial sign alone proves that the
locally soluble **marked cover has no rational point**. For instance B,
the normalized radical is precisely the line \(\langle F\rangle\),
so the marked class is Selmer-four liftable. Classical Kummer and
Cassels–Tate duality identify its dimension with the full
2-primary Selmer corank plus the even dimension of \(2F_{\Sha}[4]\),
where \(F_\Sha\) is the finite nondivisible 2-primary quotient.
Consequently instance B has full 2-primary Selmer corank exactly
one. Invoking the same [version-pinned pointwise 2-converse,
Theorem 1.1](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/A-pointwise-2-converse-for-elliptic-curves-with-rational-two-torsion-October-7-2026/build/sections/introduction.tex#L12-L42)
as a **separate external input** gives rank one and realizes the
unique radical line by a rational point, hence the *abstract
numerical* marked \(C_{a,b}(\mathbf Q)\) is then nonempty. No rational
coordinates, rational localization at the named cells, or ambient
full-contact PointPair follow from this statement.

## Numerical scope and replay

Both \(b\)'s are nonsquare units at \(23\mid B\). Negative depth of
\(W\) there is impossible on either auxiliary cover (it would
force \(b\) square by the \(t\) equation). They are therefore
not instances of the original full-\(B\) saturation. This is not
an obstruction to the covers being locally soluble at 23 by
ordinary unit charts. Neither global rank claim nor the proof of
nonemptiness requires treating this optional restricted numerical
capsule as an original prepared four-pole witness.

The optional wheel generating the fixed-\(p_a\) companion retains the
exact sixteen-bit prescribed phase 6693 and the six fixed Legendre phases.
At 415721 the corresponding bit comes from \(p_a^{-1}(W^2-s)\);
elsewhere it comes from \((W^2-s)/p_a\). On the finite range
\(76176<q\le10^9\), the five-small-prime wheel modulo
\(8\cdot3\cdot5\cdot7\cdot11\cdot37\) has 540 classes, with eleven
integer survivors of the exact full phase, two primes and one valid
finite oriented output. This bounded exploratory claim is not
needed to verify a certificate or a lower bound on every possible
producer. The default proof replay verifies the supplied primes and
does not scan for candidates. From within this directory:

    for j in 1 2; do
      python3 check_exact_two_factor_local_cover.py "$j" 32768 | cmp - "EXACT-TWO-FACTOR-LOCAL-$j.json"
      python3 check_numeric_selmer_rows.py "$j" | cmp - "EXACT-NUMERIC-SEL2-$j.json"
      python3 check_frozen_cassels_witnesses.py "$j" | cmp - "VERIFIED-NUMERIC-CASSELS-$j.json"
    done

For provenance, the optional tangent search uses SymPy; the pinned
replay never trusts or needs its solver. The earlier same-scale
fixed local Kummer rules and degree-four interpretation are the
same mathematical source as the previously reviewed paper and have
not been changed here.
