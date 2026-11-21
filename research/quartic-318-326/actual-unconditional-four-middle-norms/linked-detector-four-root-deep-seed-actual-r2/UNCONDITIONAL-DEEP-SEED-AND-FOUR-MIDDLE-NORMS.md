# An explicit nontorsion point gives all four middle-root norms, including the dyadic guard

This extends the previous unconditional nineteen-cell, odd and real
construction with the missing deep dyadic seed. No rank or analytic
converse is invoked. It concerns **the same archived repaired
\(J,h\), four literal middle factors and nineteen contact cells**.
The rational \(W\) is proved to exist via finite-place congruences and
a real rotation; no expanded giant \(W\) is claimed.

## The donor point on a simple square-parameter member

Use the exact two pair templates of the predecessor. For \(L_i=u_i^2\),
write \(\lambda_i=K_i(L_i)/L_i\). With \(u_1=1,u_2=1/2\),
\[
 (\lambda_1,\lambda_2)=(41/32,\ 1275400596441/7626746323592).
\]
On the smooth curve \(E_*: y^2=x(x+\lambda_1)(x+\lambda_2)\) take
\[
 P_*=\left(
 \frac{35441651962058444737857}{55614360877956828839800},
 \frac{183352115295979214553073483792738784397}
      {184873626882008858208518823599138314000}
 \right).
\]
The exact checker substitutes these two fractions. Scale by
\(X=d^2x,Y=d^3y\), \(d=7811144=8\cdot407\cdot2399\), to the
integral model with \(A=d^2\lambda_1=78174149816818\) and
\(B=d^2\lambda_2=10203204771528\). The prime 71 is good, and
\(v_{71}(X(P_*))=-2\), so the point in the 71-adic formal group
has depth 1. That group is torsion-free by its formal logarithm,
so \(P_*\) is nontorsion. The proof requires no assertion that it
generates the rational group or that a rank program found its full rank.

## One seed deep at all the finite places, without factorization

Let \(\mathcal S\) be the nineteen actual contact primes together
with \(2,3,5,7,11,17,37,2399\). At each \(p\) use the formal subgroup
of the fixed integral model just displayed. It is an open
subgroup of the compact group \(E_*(\mathbb Q_p)\), hence has finite
index. A common integer multiple of all these finite indices,
and of 2, brings \(P_*\) into every formal subgroup.
Multiplication by \(p\) increases positive formal depth: the linear
term of \([p](z)\) has valuation \(v_p(z)+1\), and all higher
terms have valuation at least \(2v_p(z)\); the point remains
nonzero by nontorsion. Multiplying by the other primes
preserves depth (unit linear coefficient). Consequently an even
integer \(M\) may be chosen so that \(Q=[M]P_*\) is arbitrarily deep
at all these places, simultaneously. For any requested integer
bounds one may simply multiply the initial index multiple by
a sufficiently high product of prime powers.

The Kummer tuple of \(Q\) is trivial because \(M\) is even.
None of its three factors is zero and it is not infinity.
Thus \(x(Q),x(Q)+\lambda_1,x(Q)+\lambda_2\) are rational squares.
Choose the rational nonzero square root \(W_*=\sqrt{x(Q)}\)
and \(S_i=u_i\sqrt{x(Q)+\lambda_i}\).
They satisfy both exact split-parameter equations, and hence both
pair products are rational norms in \(\mathbb Q(\sqrt2)\).
At each guarded prime, the integral formal model has
\(v_p(X(Q))=-2v_p(z(Q))\), so
\[
 -v_p(W_*)=v_p(z(Q))+v_p(d)>0.
\]
Take seed depth at least 600 at 2, at least the desired odd
depths at the seven other small primes, and any positive depth
at each of the nineteen cells. This step does **not** ask this
even multiple to already land in a prescribed contact cell.
The guard depths may be chosen as exact values above the initial
minimum by selecting the exponents individually. The construction
can also just use higher depths, which suffice at the small places.

The two rational norm equations at this new \(W_*\) supply
points on the two parameter conics, which now allow **independent**
rational choices of the \(L_i\). They do not require \(L_i\) to
stay rational squares globally. This is the second, odd-multiple
stage below; the two stages use different elliptic curves.
This is not an even/odd contradiction on a single rank-one orbit.

## Transfer from a deep seed to the original cells and real threshold

The previous odd-multiple argument continues to work with a
nonintegral seed at the nineteen primes. At \(p\) choose \(D=-v_p(W_*)>0\)
and \(N>D\), then choose \(L_1,L_2\) close to
\(p^{2N}d_1^2,4p^{2N}d_2^2\). The seed equation has a local square
because \(L_i W_*^2\) has positive valuation and \(K_i\bmod p\)
is still the same nonzero square. The desired \(W_p\), a unit,
also gives actual local points on the corresponding conic
intersection. The good model has \(\widetilde x=p^{2N}W^2\) and
the two constant shifts reducing to \(1/2,1/8\), exactly as before.
Translation by \((0,0)\) gives formal depths \(N-D\) for the
seed and \(N\) for the unit target. Their logarithm ratio is an
element of \(p^D\mathbb Z_p^\times\), not a unit, but it is an
ordinary admissible congruence for the **odd** multiplier \(m\)
at this odd \(p\). Since the translation torsion point is fixed by
odd \(m\), it reaches the exact target \(W_p^2\bmod p^2\) at every
one of the nineteen \(p\). The resulting new point \(P_0\) is
nontorsion by its nonzero odd-\(p\) formal translate.

At every one of the eight guarded small primes, take the new
\(L_i\) sufficiently close to 1. They are local squares, the
seed is already as deep as needed and the two seed equations
are local squares by domination over the fixed \(\lambda_i\).
The scaled integral model from the previous proof applies; choose
\(m\) prime to each odd guarded prime, and odd at 2. A unit
linear term with all other formal terms deeper preserves formal
depth, at 2 as well as elsewhere, so all eight seed depths are
exactly retained. CRT is unchanged since the sets of primes are
disjoint. The same positive real sign choice for the \(L_i\) and
density of the one progression of multiples give arbitrary large
positive \(W\), for this same fixed \(h\) and middle scaling.

The argument for both separate pair norms, followed by splitting
every odd inert valuation individually, is the same as the
predecessor: there is only one factor of a pair at a unit root,
and at the fixed root denominator/difference primes negative
\(W\) dominates by the guard. The two pair differences and denominators
are all covered by the odd guards above (apart from the ramified 2).
This proves the four literal middle factors individually norms.
It is an unconditional construction.

## Exact original small-place integration and limits

The earlier literal three-pole small-place proof applies to
the same \(h\) and any deeper \(W\) at 2 and 3. At 17 the same
explicit weight estimate improves with increasing negative
depth, since all three \(c\) scales are units at 17 and all sixteen
unweighted coefficients are integral. Thus these simultaneous
\(W\)'s give the three nonzero local square pole values at each
of \(2,3,17\), with the old required lower depths \(3,1,2\).
The nineteen archived \(W\)-squared cells are unchanged and the real
\(W\) largeness is unrestricted.

This does not keep the earlier *complete global* \(a,b\)
squareclasses. More importantly, the remaining odd split support
of the four middle factors lacks a full elliptic order analysis,
and the other eight nonzero root factors on the two outer
scales have not been globally controlled. The full three
square denominators, rational PointPair witnesses and original
quartic theorem therefore do not follow.

## Replay

    python3 check_exact_deep_seed_point.py | cmp - EXACT-DEEP-SEED-POINT.json

The optional positional argument is the prior exact checked
nineteen-cell JSON at its pinned digest. The local lifting proof
does not expand either global index multiple. Exact Fraction
verification of the donor point and its formal nontorsion
certificate suffices. A rank search was used only to discover
the fractions, not to certify any assertion.
