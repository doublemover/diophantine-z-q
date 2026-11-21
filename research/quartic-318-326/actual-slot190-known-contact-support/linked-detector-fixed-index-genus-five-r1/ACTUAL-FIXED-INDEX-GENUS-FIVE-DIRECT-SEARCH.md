# Fixed h restricts even arbitrary rational t to a finite genus-five family

This removes the square-denominator restriction from the finite
t conclusion in the independently verified fixed-index obstruction
dd5d6ca1…. Fix the genuine original 16-leaf detector coefficients
at any guarded h with w37≠0 and its fixed nonzero scale c.
Do not change other pole or point data. The theorem is already
necessary to find a literal PointPair **for just this one detector**.
It gives no actual rational t or pair.

Write T=c²t=u/v with primitive integers (u,v), v>0 and
take the five original contact linear numerators

    G=(u, 2u+v, u+v, 2399u−v, 407u+32v).

They are all nonzero at any valid nonzero pole:
F(T)=(∏G_i)/(2·2399·407·v^5).
Start from the fixed finite exceptional set S in dd5d6ca1…;
enlarge it by primes dividing the five leading coefficients
or pairwise determinants. The ten exact determinants in
lexicographic pair order are
1,1,−1,32,1,−2401,−343,−2400,−375,77175.
In particular their only prime factors are 2,3,5,7.
This is a set fixed **before** arbitrary rational t; no bound
or computable factorization of the rest of S is asserted.

For p outside S, if p divides v none of the G_i vanish mod p
because p∤u and all leading coefficients are units. If p∤v,
two zero G_i would give u=v=0 mod p by the nonzero
determinant. Thus a positive v_p(G_i) is the whole positive
v_p(F(T)), and is even by the literal PointPair obstruction.
Consequently each nonzero integer G_i has signed squareclass
d_i supported on S. This does **not** require v to be a square:
the ratios already eliminate its denominator class.

For each of the finitely many choices d_0,...,d_4,
let d'_i=d_i/d_0 and consider the actual normalized
multiquadratic cover of the T-line,

    Y_i² = d'_i (a_i T+b_i)/T,   i=1,2,3,4,
    (a_i,b_i) as in G_i above.

Every valid t lifts to a rational point on one such cover away
from the five contacts: take the ratios of the four square roots
of the split G_i relative to G_0. The cover is geometrically
connected, degree 16, since at private contact i exactly the
i-th radicand has odd valuation, proving independence in the
geometric function field. Its branch points are the five distinct
finite contacts. At each private contact the inertia has order 2.
At T=0 each radicand has a simple pole; after geometric completion
all units have square roots, so the common local ramification still
has index exactly 2, not 16. Infinity is unramified (all four
ratios are units). Smooth projective normalization therefore has

    2g−2 = 16(−2)+5·8 = 8,    g=5.

By Faltings (1983, [original paper](https://geodesic.mathdoc.fr/item/IM_1983__73_143051/)),
each cover has only finitely many rational points. Since c≠0,
there are only finitely many *arbitrary rational* t that can
pass a single detector at this fixed h. This remains a necessary
finite reduction, not an effective global proof or an obstruction
to choosing h after contact support.

## Exact finite algorithm when a class tuple is proposed

For a concrete tuple d'_i there are five explicitly available
elliptic quotients. For I nonempty choose the character that
multiplies the signs at i∈I; after clearing square poles its
quadratic quotient is

    Z_I² = (∏_{i∈I} d'_i) T^(|I| mod2) ∏_{i∈I}(a_i T+b_i).

Exactly |I|=3 or 4 gives degree four and four rational distinct
branch roots; choose any branch root as elliptic origin.
These are the four three-index quotients and one four-index
quotient. Other nontrivial characters give genus zero. The
5 elliptic quotient Jacobians are enough, up to isogeny, for
the whole genus-five Jacobian: under the rational sign action
their pullbacks on differentials lie in five independent
character eigenspaces, each dimension one, exhausting g=5.
Equivalently the sum of the five pullbacks on the Jacobians has
full rank on its tangent map, hence is an isogeny in characteristic
zero (use the character projections, or dualize the quotient
pushforwards). No independence of arithmetic twists is asserted.

An independently certified rank-zero result for even **one**
of these five quotients gives a finite checkable list of candidate
T for that specific d tuple via its exact rational torsion,
before testing the remaining signs and literal PointPairs.
If none has rank zero, the Jacobian decomposition still bounds
the actual Chabauty rank by their rank sum when applicable.
This is a practical path if S is manageable or a candidate tuple
is known; it does not by itself enumerate S for the actual
enormous fixed h, and no rank or point of an actual tuple is supplied.

The adjacent exact checker records the determinants, genus
combinatorics and all five rational cross ratios and j-invariants
(up to Legendre permutation) of the unchanged branch sets.
It is not a rational-point search.

```sh
python3 -B check_contact_genus_five.py | cmp - EXACT-FIVE-CONTACT-QUOTIENTS.json
sha256sum -c SHA256SUMS
```
