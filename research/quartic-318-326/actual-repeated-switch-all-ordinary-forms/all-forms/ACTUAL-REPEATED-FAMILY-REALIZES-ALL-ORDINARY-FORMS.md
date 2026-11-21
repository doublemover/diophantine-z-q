# Every ordinary quotient pairing is attainable after the actual finite switches

Use the exact finite type A then type B pair construction of
6bce1645, its final fixed old-b-clone normalization and full marked
re-tuning 933b5ed7. It keeps the actual same XVI roots, original
sixteen balls, and each newly added true t-root contact. Every
literal same-line subspace of the final normalized V_k is zero.
Let H_k be its explicit recursive complementary plane.

**Result.** One may first choose H_k hyperbolic and the entire
marked row zero, and then realize **every alternating pairing** on

    Q = V_k/(H_k + <F_*>)

as the ordinary Cassels pairing after projection orthogonal to H_k.
This works on a single fixed allowed order cap and Gaussian ray after
the hyperbolic choice. No numerical class dimension or parity is
asserted. The ordinary normalized maximal rank is consequently
2 + 2 floor(dim Q/2). If dim Q is even, a unique marked radical line
is attainable. If it is odd, the minimal normalized radical dimension
is two. Neither parity, a pointed lift, an actual rational point, nor
all remaining factor conditions are consequences of this note alone.

## 1. Recovery of a new hyperbolic plane

At either prime of the **last** pair, inertia fixes all earlier
quadratic support and evaluates H_k(T) as T through chi_{d_k}.
The marked class is locally trivial at this prime. Apply the exact
square-inertia argument of 5448017e there, with the final admissible
marked reference of 933b5ed7. That prime is retained and stripped
from all order fields; only its separate Gaussian ray can be
ramified. A tame unit nonsquare on one component has square image
there, so preserves every prescribed quadratic unit sign. Choose it
avoiding the at most eight residues whose square times the current
coordinate would enter mu_4. The square is central on the full cup
governor (all cocycles have exponent two), toggles the H_k pair by
e_2(T_0,T_s)=1 and leaves every marked bit zero. It preserves the
Gaussian group-count exclusion. The previous exact finite/odd-tail
prime realization applies. Keep that ray choice fixed below.

## 2. The original pure color evaluations on Q are unchanged

Factor every switch as V_j = V_{j-1}^0 + H_j, where the old local
evaluation at the chosen pair is an isomorphism on H_{j-1}, and
its kernel V_{j-1}^0 contains F_*. All H_j have character support
only in a and the preceding paired products d_l. The exact old
pure inertia roster 19ea8721 avoids p_a,q_a and these added
contacts (they are outside all old support and old contact primes).
It also avoids the bad order prime 7. Its p47 marked correction
still applies. Every old pure lambda_i(-)T_i thus kills H_j and F_*
and has the same evaluations on the common V_{j-1}^0. Inducting,

    V_j/(H_j + <F_*>)  =  V_{j-1}/(H_{j-1} + <F_*>)

canonically through the common strict space modulo the mark. The
three L_i and D_i=Ann(L_j+L_l) are literally the old ones under this
identification, not guessed from a list of tested primes. The old
span equality and its consequence that the D_i sum directly persist.
The mixed-color shifts are legitimate by the all-good-odd order
kernel argument c3bacbd4 and fill the forms vanishing on all
D_i×D_i by ca6f4fba. It remains to free the three diagonal blocks.

## 3. Only a space of dimension at most one can resist in any block

Use the matrices C_A, C_B of the two fixed switching phases.
At a later pair all previous d_j evaluate trivially and a evaluates
nontrivially. Consequently on that pair H_{j-1} evaluates exactly
as C_{j-1}, and the recursion can be written

    H_j C_j^-1 = H_{j-1} C_{j-1}^-1 + chi_{d_j} C_j^-1,

starting with H_0=chi_a I and C_0=I. Therefore, if D_A and D_B are
the products of all type A and type B pair products, the final
H_k has coordinate characters in the three-dimensional span
of (a,D_A,D_B). Both phases are nonempty because the original
H_0 contains a nonzero in each S_i, and Phase A keeps its middle
line until Phase B begins. The last pair is type B. Distinct
paired supports ensure the characters a,D_A,D_B are independent.

For a color T_i take g in G_{Q(i)} killing chi_a, chi_{D_A},
chi_{D_B}, and the i-th coordinate character (F_*)_i. Then

    mu_g(F) = e_2(F(g),T_i)

kills H_k and F_*. Let K_i be the common kernel on D_i of the
mu_g. By elementary multiquadratic Galois theory it consists
exactly of the classes admitting an i-th coordinate in

    span(-1, a, D_A, D_B, (F_*)_i).

Passing to a different representative by H_k or the mark does
not change this condition. Use the unique strict representative
modulo F_* in the last V_{k-1}^0. Such a representative has no
new last-pair valuation, so the D_B coefficient is zero (the
last pair occurs in D_B and not any other displayed class).
The representative is locally trivial at that pair. Multiplicative
unit evaluation there kills the a coefficient: a is nonsquare,
whereas -1, D_A, and (F_*)_i are squares there by the actual
common phase conditions. Remove the remaining mark coefficient
by adding F_* itself. This choice is unambiguous: (F_*)_0 has
class 2399, and (F_*)_s,(F_*)_t have odd depth at 47, unshared by
-1 and the moving products. We obtain a linear injective map

    K_i -> span(-1,D_A)

by taking that i-th coordinate: a zero coordinate would put
its actual final representative in S_i=0.

The image has no pure -1, and thus dimension at most one.
Here it is essential to use the exact old coordinate tables,
not assume a sign defect vanished after changing the family.
Transport its representative back through each common strict
space by subtracting the appropriate H_j class. This does not
change Q, and changes each coordinate by a product of a and the
d_j. Suppose its final i-th coordinate were -1. All pair supports
are disjoint from every original normalized coordinate, so the
original representative has coordinate in the class of -1 times
a power of a. The old calculation 4de5369a shows that the kernel
of the i-th coordinate modulo span(-1,a,(F_*)_i) on D_i is
exactly the old B_i: this follows from the literal coordinate
lists of 19ea8721. Therefore that original representative can
be adjusted to genuine coordinate 1 by adding old H_0 and the
mark. Both have positive rational i-th coordinates, so they
cannot remove the negative real sign of -1 times a power of a.
Contradiction. Thus the only potential invisible direction is
at most one linear combination involving D_A, not an unseen
multidimensional same-line space.

## 4. The full alternating variation

For lambda_i in L_i use the actual good odd pure inertia sum
and g above. The commutator and odd-power raising supply the
shift lambda_i wedge mu_g on Q. L_i restricts onto D_i^*, and
the mu_g restrictions span Ann(K_i). These wedges therefore
realize all alternating forms on D_i vanishing on K_i×K_i.
As dim K_i<=1, **every** alternating form on D_i has this
property. The same shift leaves other D_j diagonal blocks
untouched because lambda_i kills those D_j. The already exact
pure mixed wedges reset all inter-block entries, giving all
of Alt(Q). All shifts kill H_k and the mark, and can be combined
as one central Frobenius modification. For each modified class
the same exact finite support, Chebotarev and independent old
odd tail preserve the actual source and all selected phases.

Hence all alternating matrices on the quotient are genuine
ordinary choices. Alternating elimination gives maximal rank
2 floor(dim Q/2); including H_k adds two and including the
rational torsion classes adds only radical vectors. The marked
rational-point criterion still needs even dim Q and the
separately stated external corank-one theorem or an independent
actual positive-rank point. This result does not assert either.

Signed: independent reviewer /root/high_review_ci. Paper/source only.
