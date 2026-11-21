# Independent review: mirror ray pairing and stricter ordinary-class certificate

Bound to exact mirror note 6036b39ca98f618daf35d598d53541d60726d91407429c2ca897c995e14ae5f4,
manifest 64446a971e88c9725dd74454d1fe58336028f31b5860a69c382d7f90f6d9da16;
and exact strict note d0e0004b8220c6a76ea9d0484dc0ce945d7d4fdb5c8f5352601bf90bb3af6b67,
manifest 45ff89f2e7cca7ee54ad96c2034179528db4c42a40f09a562ff894684caf5735. Both author finite arithmetic outputs reproduced byte for byte.

For the same actual point field, the unit coefficient μ transforms by b;
the λ=a part pairs perfectly with ξ=b/a **on the ray group**. The
cyclotomic overfield T descends its diagonal-invariant elementary
characters to the actual covector field: index 12 is prime to 13
and both positive-degree obstruction groups vanish. At each matched
13 pair the restriction into the single T completion is injective
by degree-12 transfer. At the tame formal side, removal of the fixed
mirror prime from the modulus also forces locally zero, not just
unramified: its Frobenius class is invariant, hence killed by ξ.

At the wild mirror place the covector stabilizer diag(1,d) has
surjective determinant, so the field lacks μ13. Its fixed formal
point gives parameter depth 13 and leading relative scalar a; since
the residue is F13, the uniformizer has the same tangent character.
On grade j the character is a^j. The 13th-power binomial boundary
at j=13 gives 169 with no cancellation: otherwise 13/π^156=-1 in
residue, and Hensel would give a twelfth root of -13 by multiplying
π^13 by a unit. That generates the same tame field as μ13, by the
cyclotomic Eisenstein relation and unique principal 12th roots, a
contradiction. Logarithm proves all depths at least 170 are powers.
The two candidate grades 13 and 169 are killed; grade 157 survives.
This gives precise local ray exponent 158 for the ξ units, not a
global conductor minimum or a computed ray quotient.

The stronger ordinary-class implication follows by taking the strict
kernel at Q13. Its images at both point places vanish, hence so do
the matched mirror characters after transfer; they are unramified
at every other place already. At every transvection test its
localization kills the known projected mirror ideal. Conversely, a
class from the ordinary ξ part is locally zero at both fixed mirror
13 places, since its unramified Frobenii are invariant. The same two
local zeros descend to the point field and all good tests force
global V descent. At w+ zero gives the actual ordinary line; in the
nonformal w− field that line injects. To see this, pass to the
unramified degree-12 field k': the true Kummer line belongs to ψ,
whereas the ordinary extension defining the nonformal point field
belongs to ψ². After adjoining μ13 by degree 12, the cyclic
degree-13 extension kills exactly its own Kummer line. The distinct
ψ and ψ² exclude killing the ordinary line. Thus the all-tests
ordinary dual is exactly the strict Selmer subgroup, while a finite
list gives only an upper bound. The actual ordinary local line has
dimension one, so a certified ordinary projected quotient of
dimension at most one would suffice for total finite dimension ≤2.
No such quotient, Selmer rank, or rational point is computed.

Using independent explicit polynomial arithmetic and binary group
addition in F_(53^13), I recovered the literal B and Z coordinates at
the archived mirror address, their degree-13 polynomials, and the
norm 26036721925606486195973. This is the true degree-13 prime
matching the original moving residue calculation under the cyclotomic
choice, not a global identification of the fields. The independent
replay takes point-field, transvection-53, mirror-53, and exact field
discriminant JSONs in that order.

The separate factor-base comparison uses [Grenié–Molteni,
Corollary 3.8](https://arxiv.org/pdf/1607.02430) (arXiv v5,
p. 10), whose ordinary generator-norm bound assumes GRH.
The integer 148614287 is a valid upper estimate for the specified
4.01 log² discriminant ceiling, and the exact first test ideal
norm is more than 10^14 times larger. This is not a complexity
lower bound. GRH is not used in the strict or ray algebraic criterion.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
