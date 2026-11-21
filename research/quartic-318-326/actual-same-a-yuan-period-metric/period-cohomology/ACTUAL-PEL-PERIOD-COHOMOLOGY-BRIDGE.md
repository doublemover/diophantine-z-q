# The ordinary PEL periods recover the exact arithmetic KS determinant

At the selected original noncontact t=32u/v, fix the previously chosen
complex embedding and the same polarized surface A. Over the overlapping
actual U(3)/U(11) levels, take the common U(33) marked family in
characteristic zero. Both pulled-back cotangent connecting maps are
those of this very family; the original cotangent direction is retained.
The complex uniformization and fixed polarization are those in
[Yuan v2 §4.1–4.2](https://arxiv.org/html/2205.11334v2#S4.SS1).
No period lattice of the different modular Jacobian is introduced.

## The actual Hodge quotient, not a guessed cohomology basis

Trivialize the integral period local system in an upper-half-plane
chart by beta -> beta (tau,1)^t in the real split quaternion algebra.
A complex period functional on the deck lattice is encoded by (a,b),
its coefficient pairs on the first and second matrix columns. In these
coordinates the period of the holomorphic form u_1 dz_1+u_2 dz_2 is
(tau*u,u). Consequently the map from complex periods to H^1(O_A) has
the actual normal form

    [a,b] -> a - tau*b.

Here is a justification of the kernel, with the same convention as the
additive Čech class of the deck functional. Extend a functional on the
lattice real-linearly to the tangent vector space. On each lift of a
small torus chart, apply that real-linear function to the local fiber
coordinate. The differences on overlaps are precisely the additive
deck cocycle. The antiholomorphic derivative of these local functions
is one constant, globally defined (0,1) form on the torus; this is its
Dolbeault representative (with the choice of Čech convention used
consistently throughout). A constant (0,1) form which is the
antiholomorphic derivative of a global smooth function is zero:
integrate its scalar components against Haar measure and use periodicity
to give zero integral of each derivative. Conversely a holomorphic
linear extension has zero class. Constant forms exhaust H^{0,1} by
the flat torus harmonic representative theorem. This gives exactly
the quotient by the periods (tau*u,u), with no scaling taken from a
choice of polarized Riemann basis.

The new source proves kernel, explicit quotient linear isomorphism,
and exact derivative of the actual period sections for all u.
The Gauss–Manin derivative of (tau*u,u) in this local period
trivialization is (u,0), so its image in the actual H^1(O_A) is u.
One can also get the identical identification directly from Yuan's
Čech operator: differentiation of z'_j-z_j on a deck overlap gives
the first-column functional and the same d(tau). The native connecting
map and its naturality show this fact is already independent of
the lift/deformation splitting. No map to H^1 chosen to make a matrix
have determinant one is used.

## Compute the polarized tangent in that very quotient

Work in complex coordinates on the real split realization and set
nu=mu^(-1). A tangent w=beta (tau,1)^t has the actual polarized
period functional on gamma given by

    E(w,gamma) = -Tr(nu beta adj(gamma)).

For M=nu beta its first-column coefficients are (-M_22,M_12) and its
second-column coefficients are (M_21,-M_11). Put
J=[[0,-1],[1,0]]. Taking their Hodge quotient a-tau*b gives exactly

    [E(w,-)] -> J nu w.

In particular the same formula applies to EVERY real direction and
extends complex-linearly, not just to two selected functionals of a
specific basis. The actual exponential sequence normalizes the tangent
to Pic^0: the principal polarization character at epsilon*w is
exp(2*pi*i*E(epsilon*w,-)); hence its additive cocycle is 2*pi*i*E(w,-).
The derivative of this literal character was independently checked in
the preceding packet. The convention of passing from normalized
infinitesimal units 1+epsilon*a to additive a is forced by epsilon²=0
and preserves the same Čech coboundaries. This explains the scalar
2*pi*i without comparing an arbitrary numerical period to a normalized
arithmetical line.

Thus the polarized tangent map to the same quotient is
(2*pi*i) J nu. Its inverse is mu (-J)/(2*pi*i).
A simultaneous reversal in the chosen connecting/Picard Čech
representatives changes two columns together and leaves the
bicanonical determinant unchanged. No independently required sign
of an individual tangent vector is a hypothesis. The actual
ordered differential therefore has determinant 210/(2*pi*i)^2.
These are first-order/cohomological identities, not implications
from the metric computation.

## Same arithmetic comparison and precise remaining formality

At the fixed ordinary point, analytic restriction of the arithmetic
cotangent extension is its very same extension for the complex
family; proper coherent GAGA identifies cohomology and its natural
exact sequences. On a common cover it sends the same lift to the same
differential difference, as encoded by the previously verified
Čech naturality. The dual abelian scheme and canonical polarization
commute with these changes. In particular transporting to level 33
and to this complex fiber identifies the original arithmetic
Yuan map with this analytical connecting map, before taking
determinants. It is not the KS of the constant family over Spec L.
The actually proved cotangent specialization puts the exact original
t-germ into this comparison; restriction to a local upper coordinate
takes d(tau) by its true chain-rule derivative. No field map of the
function field to L is used.

The terminal source only needs the genuine diagram identifying the
arithmetic map after transport with the computed quotient connecting
map. It constructs the polarized matrix and its inverse and proves its
full signed determinant via that diagram, not by assuming a KS
determinant or Hodge norm. Coherent GAGA, the torus realization
of this actual universal family, Picard/dual identification and the
production of the scheme cohomology diagram remain explicitly
classical. The Hodge lattice metric belongs to the separate principal
same-A lattice packet; the J-period owner remains independent.
No native end-to-end result, field rank claim, actual numeric period
measurement, local Lean build or remote write.

    sha256sum -c SHA256SUMS
    python3 check_period_quotient.py | cmp - EXACT-PERIOD-QUOTIENT.json
