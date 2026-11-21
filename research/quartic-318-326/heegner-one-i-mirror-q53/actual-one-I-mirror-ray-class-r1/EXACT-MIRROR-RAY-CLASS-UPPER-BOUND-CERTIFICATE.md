# An exact ray-class upper-bound certificate without a Kummer basis

Use the actual historical base d=2811626664334219040035976315,
its original point field F=Q(P), line field K=Q(<P>), and
[exact transvection sieve](../actual-one-I-incidence-selmer-r1/EXACT-TRANSVECTION-IMAGE-TEST-FOR-ACTUAL-SEL13.md).
Put T=F(ζ13); write G(T/K)=Δ×Γ by scalar action a on P and
cyclotomic action b on ζ13. The original character is λ=a.
Define ξ=b/a and F^c=T^(ker ξ), the actual degree-168 covector
field. This gives a basis-free upper-bound certificate through
one explicit finite ray class quotient; it does not compute
that quotient or give a class-rank bound.

## 1. Perfect pairing in degree 168, not 2016

Restriction identifies the original ambient A=F(S,13)_λ
with T(S_T,13)_λ. The extending degree is 12, prime to 13,
so invariant Kummer descent is exact by restriction and norm;
valuations outside 13 remain multiples of 13 in both directions.
On T the full S_Kummer space is dual by the Kummer pairing
to the maximal abelian exponent-13 quotient unramified
away from 13, a finite class field. At primes away from 13
this is precisely the unramified criterion for valuations
divisible by 13; at 13 a sufficiently deep ray modulus
contains all conductor possibilities. There is no real
place condition at this odd prime.

Under the simultaneous Δ×Γ action, the pairing into μ13
transforms by b. The exact paired character with λ is thus
ξ=b/a, not its inverse. This character is trivial on the
diagonal order-12 subgroup, whose fixed field is F^c.
In fact T=F^c(ζ13), so T/F^c is cyclotomic and unramified
outside 13. Restricting exponent-13 abelian characters
unramified outside 13 to T identifies them with the
diagonal-invariant characters of T: both obstruction groups
for the diagonal vanish because its order is prime to 13.
The same statement locally follows by restriction/corestriction.
Thus the ξ piece of the dual space is the corresponding
ray class quotient over F^c, with no degree-2016 class group
needed. Equivalently A pairs perfectly with the ξ-eigenspace
of the elementary 13-ray class group on this degree-168 field.

## 2. Formal ordinary zero removes one of the two modulus primes

The two p=13 primes in F^c have (e,f)=(1,12) and (156,1)
by the exact covector action. Call them w0 and w_ram,
respectively. Over the formal line local orbit, F has
e=12,f=1 and F^c has e=1,f=12. They embed into the same
T completion e=12,f=12. Restriction on either side has
degree 12 and is injective on elementary cohomology.
Therefore the original local condition that the Kummer
class vanish at the formal point prime is exactly that
the reflected character be locally trivial at w0.

Since w0 is fixed by the relative scalar Galois group
of F^c/K and ξ is nontrivial, any unramified ξ-character
is automatically trivial on its one-dimensional valuation
line (the Frobenius class of this fixed prime is invariant).
Thus imposing the formal zero is equivalent, in this
eigenpart, to removing w0 entirely from the ray modulus.
Only w_ram remains.

### Exact faithful local depth at w_ram

The local covector stabilizer for c=(1,0) in the upper
Borel is diag(1,b), so its determinant is surjective;
the corresponding field does not contain μ13.
It fixes the actual nonzero formal torsion point P_+,
whose parameter t(P_+) has absolute valuation 1/12,
or valuation 13 in this ramified covector completion.
The relative degree-12 action over the line field
can be represented by diag(a,b) on the two lines,
with ξ=a. It sends t(P_+) to a·t(P_+) in the leading
term. If pi is any normalized uniformizer, the action
on its leading term is therefore a as well: t(P_+)
is a unit times pi^13 and the residue field is F13,
so a leading scalar raised to the 13th power is itself.
It follows that the grade U^j/U^(j+1) has character a^j.

Here v(13)=156. The usual local logarithm implies units
of depth at least 170 are 13th powers. The possible
leading depths of a 13th power on principal units are
13j for 1≤j<13, 169 at j=13, and ≥170 for j>13.
The boundary case j=13 is genuinely 169, not canceled:
its leading coefficient on (1+c·pi^13)^13 is
c^13+(13/pi^156)c. The unit 13/pi^156 cannot reduce
to −1. Otherwise Hensel yields a root of (-13)^(1/12)
by multiplying pi^13 by a unit; that root generates
Q13(μ13). To check this last equality, expand the
cyclotomic equation for s=ζ13−1: s^12/(-13) is in
1+(s), has a 12th root, and both tame Eisenstein
extensions have degree 12. All 12th roots of unity
already lie in Q13. This contradicts the exact local
determinant observation above.

Consequently the only graded unit contributions of
character ξ are

    1, 25, 37, 49, 61, 73, 85, 97, 109, 121, 133, 145, 157.

Indeed grades j≡1 mod12 are the only candidates; grade
13 is killed by the 13th power of a depth-one unit,
and grade 169 is killed by the just verified boundary
map. Taking the ξ projection is exact since 12 is
prime to 13. Grade 157 survives because no power has
that leading valuation. Thus the ray exponent **158**
suffices and is the smallest universal local exponent
for the faithful unit characters of this completion.
It need not be the smallest conductor of the global
character quotient.

## 3. A finite transvection test adds one honest ideal relation

Choose any good transvection prime ell and a nonfixed
degree-13 point-field prime used by the previous sieve.
Choose a local root ζ13: ell≡1 mod13, so T/F and
T/F^c split at the relevant local primes. The matching
F^c test prime q_ell is also degree 13 over ell and
has the very same completion after the compatible
choices in T. No global field isomorphism is involved.
The residue Kummer test is the pairing with its
unramified Artin Frobenius. Thus passing at ell means
exactly annihilating the projection of the ideal class
[q_ell] in the reflected ray quotient.

The enclosed finite witness gives a literal q_53 for
the earlier selected nonfixed branch: take the primitive
root 16 of order 13 in F53 and the same exact u,W of
the prior score computation. Evaluate B and the mirror
generator Z=sum_a σ_a(W) ζ13^a. Both have residue
degree 13, with their exact finite polynomials and
joint coordinates archived. In particular this supplies
a reproducible prime address of norm 53^13 on the actual
mirror field, not a generic prime or a test chosen after
an unknown global class basis. The Gaussian generator
need not generate the global maximal order.

## 4. Precise sufficient certificate and the missing ingredient

For a finite list of tested transvection primes define

    R_tests = e_ξ ( Cl_(w_ram^158)(F^c) / 13 )
                  / span{ e_ξ[q_ell] : tested ell }.

Its linear dual is exactly the part of original
A passing the formal w+ and those finite good-prime
tests. The true Selmer group embeds there, without
asserting that a finite arbitrary list detects all
global descent failures. Thus a **certified presentation
of R_tests of dimension at most 2** suffices; no global
Kummer class or unit basis need be enumerated. For this
same curve it would imply full corank one by the proved
odd parity and the usual good-ordinary 13-converse.
This is a conditional certificate, not an arithmetic result.

For clarity, the ordinary ideal class group still
contributes. Apply reduction modulo 13 and the exact
character projection to the usual ray sequence. Writing
L_w for the projected local unit quotient (dimension 13),
and modding it by the image of global units, the relevant
exact sequence is

    Cl(F^c)[13]_ξ → L_w / image(global units) →
        (Cl_(w_ram^158)(F^c) / 13)_ξ → (Cl(F^c)/13)_ξ → 0.

The first boundary comes from a prime-to-modulus ideal
a with a^13 principal and reads the local unit residue
of its generator (up to the reciprocal convention).
One cannot replace this sequence by a unit rank count,
or assume the boundary is injective or surjective.
Even if the whole local contribution were removed,
R_tests still surjects onto the ordinary projected
class quotient modulo the same tested prime classes.
Finite Frobenius removals each give at most one relation,
not a domain upper bound. A rigorous quotient presentation
needs a certified set of generators and enough genuine
ideal/local relations (or another independent dimension
argument). It is enough to prove an upper bound via
a surjective presentation; exact saturation of all
relations is not required if the bound is already ≤2.
Neither that nor a practical bound guaranteeing it is
provided here. The mirror field, like F, has 2641-digit
absolute discriminant by its equal rational permutation
character. The universal Minkowski factor-base bound
still has 1257 digits. This explains why brute-force
unconditional factor-base enumeration is not the
certificate proposed here, not a complexity lower
bound on more advanced class-group algorithms.

    sha256sum -c SHA256SUMS
    python3 -B check_actual_mirror_53.py | cmp - EXACT-ACTUAL-MIRROR-53-PRIME.json
