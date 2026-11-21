# Independent review: full marked Selmer-four lift on the actual two-class construction

**Verdict: independently checked paper proof and finite witness pass.**
This binds exact author note SHA-256
9a9c8988871912e77ae9ce651c65331432b5988334751ddb0cdc0e7d2a50ac27
and author manifest SHA-256
45899b89d72bec33bebdab8c3abb37855ef5618d5303a18e36d147291909dab5.
All frozen author analysis/control bytes were checked, and its finite
script output replayed byte-for-byte. No actual moving prime was computed.

**Fixed whole normalized space.** At the new b-prime, the four
rational torsion Kummer rows exhaust the local image and have distinct
valuation rows. Removing the unique matching rational torsion row
makes every global Selmer cocycle actually zero at this completion.
The resulting fixed subspace V is the entire 2-Selmer group modulo
rational torsion Kummer, not just the earlier known subspace W.
Changing the prime changes neither the fixed-place conditions of V
nor the other three moving-place conditions: the clone matches the
literal pilot's B-local classes, and each inter-prime Legendre bit
is the already checked +1. The normalized marked row is exactly
F_*=(t,aδ,atδ), obtained from α=(D,b,a) by its literal t-root
rational torsion class. Translation by that class is harmless in
the Cassels–Tate pairing.

**Two central inertias and their exact annihilator.** At p_a and
2399 the normalized marked row takes the independent inertia values
T₀ and T_t. The former prime is removed from the clone levels; for
the latter, the archived XVI modulus is 221 modulo 2399 and the
two Gaussian norm counts of the first clone are 1645 and 2144
modulo 2399. Thus neither first-clone order inserts 2399 into the
updated index modulus. The order-clone parts are unramified at these
two places and remaining inertia is central in the abelian ray part
over Q(i). The commutator of the normalized cup extension evaluates
as the symmetrization of the bilinear cup cochain. If a row F kills
both inertia commutators for all other arguments, it is J F_* over
Q(i) for a self-adjoint J, and over Q the sole potential extra
character is χ₋₁ times a fixed torsion vector. The exact real, Q₃,
and Q₂ Kummer images respectively confine that vector to T_s,
force J to preserve T_s, and require the cancellation in the
T_t restriction. The only possible extra row is (−aδ,1,−aδ)
up to adding F_*. It cannot be local at a fixed odd prime of odd
depth in P=407m²+32·2399n². Here P≡7 mod 8 and is prime to
2,11,37,2399 by the literal ratio rows, so at least one such prime
exists without factorization. At that prime the separate 0-coordinate
of every local Kummer class has even valuation by the exact
s,t collision table, while −aδ has odd valuation. Therefore the
commutator image is the entire dual of V/⟨F_*⟩, not a claim that
an arbitrary alternating matrix on V can be prescribed.

**Primary governing-field comparison and original selection.**
[Smith, Lemma 3.1 and Theorem 3.2, including proof equations
(3.1)–(3.3)](https://arxiv.org/pdf/1607.07860) applies to the fixed
base E_(a p_b) with the two b-prime twists. The fixed places include
bad reduction, 2 and infinity; Q has trivial class group. The twist
ratio is a square at all those places, and both normalized classes
belong to both actual Selmer groups. The governing cochains can be
taken as F₂-valued primitives by local Kummer isotropy, Brauer
injectivity, and Hilbert 90. The prescribed quadratic correction
gives governing fields unramified outside the fixed places. Both
variable primes split in the normalized cocycle fields, so the
two degree-one Artin terms are precisely the two change bits.
Choose a reference admissible prime and shift its exact Frobenius
representative by the central element supplying the reference marked
functional. That shift fixes the full original order/ray field and
all normalized elementary cocycle fields. The joint conjugacy class
is nonempty and the computed difference kills the marked functional
against all of V. Added ramification is confined to the already
excluded finite rational support, so the late Gaussian ray
intersections remain trivial and the prior positive-density,
medium-ray-bound and large-coordinate tails still apply. This use of
the governing theorem is not a GRH density claim.

By the [Cassels–Tate radical and Selmer-four comparison, Fisher,
Introduction](https://arxiv.org/pdf/2208.14977), the exact marked
class lies in the image of Sel₄ → Sel₂ for an admissible prime.
There is an everywhere-locally-soluble 4-cover lifting the actual
two-class 2-cover; the latter has Sha class in 2 Sha[4]. No numerical
new prime, explicit 4-cover equation, prescribed lifted residue
cells, rational point, Mordell–Weil rank, Sha vanishing, or Lean
formalization is supplied. No finiteness assumption on Sha is used.

Reviewed and signed: **Vesper, independent mathematics review**,
2026-11-21 UTC.
