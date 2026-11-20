# Fixed-degree necessary eliminants for a literal order-three source branch

Same actual h, i=mh and scalar c, with m divisible by 3.
At a good odd prime p outside 2·3·7·β·R(1+A), suppose both
literal h-source reductions over their relevant finite
field(s) have order dividing 3, and at least one has
order exactly 3. This is distinct from the already
tested both-zero chart and neither assumption is made
at a generic prime.

At a branch of order 3, U_h is a unit and U_i=0 in
reduction: i kills the order-three point and it is
not one of the zero/pole labels of U_h. The double
has the same abscissa x as the original residue point,
so U_h²=1/x. At a zero h branch the formal ratio
U_i/U_h is integral (signed m), and 1+U_h²/R reduces
to 1. Thus with at least one order-three branch the
total norm ratio Q is zero, and W=N².
Writing w_± for its two norm constituents,
each w is either 1 or 1+1/(Rx) for an actual
order-three abscissa at the indicated branch.
For inert √2 the two constituents are conjugate in
the finite quadratic extension, so both are of the
nonzero order-three type in this case. For split √2
all one- or two-branch possibilities are retained.

On y²=x³−d²x the division polynomial is
3x⁴−6d²x²−d⁴. Put

    f_d(w)=3−6d²R²(w−1)²−d⁴R⁴(w−1)⁴,
    d_+=3−√2,   d_-=3+√2.

Then the nontrivial options satisfy f_d(w)=0; this
substitution is valid since Rx is nonzero.
The single-variable eliminant for N=w_+w_- is

    f_(d_+)(N) f_(d_-)(N)
        · Res_w(f_(d_+)(w), w⁴ f_(d_-)(N/w)).

The first two factors account for exactly one branch
being O; the resultant accounts for both nonzero
branches. For the latter, use the actual nonzero w
directly when it is nonzero, or use the root-product
description with coefficient units when w=0. The
written resultant has no inverse in its polynomial
argument, and equals the product over both four-root
sets, up to the specified leading coefficients. In
particular all possibilities are retained even if
some w vanishes. The coefficients are rational by
conjugation/symmetry and algebraic integers, hence
integers. The leading coefficient is (7⁴ R⁸)^5,
so removing integer content cannot lose any moving
prime. The resulting degree is 24; its exact factor
degrees over Q are 4,4,8,8.

If p|H then the fourth power of N also obeys

    144β N⁴−(1+A)²=0 mod p,

whereas p|L' gives

    7056β N⁴−48(1+A)²=0 mod p.

Taking the corresponding integer resultants
with the primitive degree-24 eliminant therefore
gives literal necessary integer divisors on this
source branch and avoids expanding [h] or [i].
One may remove only the indicated fixed factors.
This is a concrete finite recurrence-derived
restriction, not the claimed actual factorization
of a global scalar coordinate.

The packet gives the exact integers (moving bit
lengths 10544 and 10528), with their four multiplicative
resultant pieces. It uses bounded factor extraction
only on those pieces, and treats unresolved cofactors
as unresolved, not prime. Every reported small prime
factor is trial-verified and independently screened
using the actual affine [h] multiplication. None
passes the literal order branch above: in some cases
both labels are O, which is correctly outside this
case, and in others a label is not killed by 3.
No new H divisor or k0-negative odd L' place is
found. In particular the unresolved exact cofactors
must not be combined with the screen to claim a
negative result on the entire order-three locus.
All other actual h residue orders and the full
specialized k0 norm remain open.
