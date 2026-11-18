# Five linked original row values with compatible exact orders

This is a finite mathematical result for **one** entire original row. Unlike
four independently selected primes it uses the five exact contact slopes at
a single parameter. The stronger example has an explicit positive common
Clearing valid on all fifteen positions for nonzero model labels. It is
**not** a fifteen-position Values record: in that example seven of the other
ten position values have explicit proper factors, and the additional
distinct prime prevents extending the particular compatible orientation.
No original integer-input assignment, trace equality, global witness,
kernel execution, or verified formal theorem is claimed.

## Strong sample: a real shared Clearing

Use labels (−1,−1,−1,−1). This is a concrete nonzero model-label tuple
(with its second label not 1), not a claim it equals the prescribed
affine labels of any integer input. In Q(i), i²=2, the model coefficient
is (3−i)² and the half-generator is R=(1+i,2i). Its duplication chart is
U(R)=2y/(x²+(3−i)²). Thus fixedRoot(1)=−1/U(R)=1−7i/4, and
fixedRoot(−1)=−fixedRoot(1). Their fourfold product is
4817/64−399i/8, of norm (−41/8)^4=2825761/4096. The three scales are
1, 3134049/4096 (real coefficient plus norm), and 2825761/4096 (norm).
The original literal roots in row order are 0, −1/2, −1, 1/2399, −32/407.
Let the Clearing denominator be

    A=2·2399·407·3134049·2825761 = 17294016221357051154.

For each of the 15 positions define k_jl=−root_l A²/scale_j². These
are all integers: A contains each scale numerator and the product of
the displayed root denominators (allowing overlap by multiplication).
Together with A>0 this is exactly the Clearing specification. Put

    w=7140,  u=6355619657003953590668572692660794222201617.

The first row's u+k_jl w² values, in the source order, are

    6355619657003953590668572692660794222201617
    7629921398233246285597621517513600811116698417
    15253487176809488617604574462334540828011195217
    21411131835217
    1205147289998231249041393360084651361989395217

All five are positive distinct primes, 1 modulo 816 and quadratic
nonresidues modulo 7. Every p comes with witnesses z⁸=−1 and t⁴=2 in Fp.
At the two roots ±r of 2 modulo p, the exact orders of the literal R
on y²=x³−(3−r)²x admit the orientation (1,1,0,0,1) using the root
listing in SHARED-CLEARING-ROW.json: bit b chooses member b as minus and
member 1−b as plus. For Π restricted to the product of these five primes,
and M−,M+ the respective **exact order LCMs**, the file supplies h such that

    h≡0 mod Π³ M−,  h≡1 mod M+,  h≡0 mod 16.

All 32 orientations are checked; exactly one satisfies these three
congruences. The supplied h and its positive period are verified by
direct remainder checks. L=16,h0=0 is a specified diagnostic, not a
claim about all continuity moduli or the actual real guard. In particular
this Π is not the product of all merged original coefficients.

## How far this same parameter actually goes

At positions (j,l) the zero-root occurrences in all three rows coincide
with u. One further prime, at (2,3), gives six distinct primes at eight
positions. The remaining seven positions have the following proper factors:

    (1,1):101  (1,2):19  (1,3):163  (1,4):23
    (2,1):41   (2,2):83  (2,4):2777.

All six primes have full certificates, both orders, and both additional
root witnesses. At the sixth prime the listed two orders have gcds 17
and 116, respectively, with the five-position M−. Thus neither may go
to plus under the already forced orientation. Enumerating the 256
assignments across eight occurrences, including the repeated zero-root
positions separately, confirms there is no extension satisfying these
three CRT congruences. This diagnosis is about a single parameter,
not a theorem excluding a full witness elsewhere.

Since the five prime values are each 1 mod 816, their product m is
squarefree and locally square at 2,3,17. The preceding prescribed-class
and canonical-anchor packets therefore apply to **this computed row
class**. This supplies substitute rational poles of the same first class;
the literal selected contact pole's complementary class, real bounds,
trace factor and original integer labels remain different obligations.

## Independent smaller sample

ROW-SPECIFIC.json uses denominator 1952786=2·2399·407 for the row
alone, w=420, u=2000262451017617, and gives five linked primes with
one compatible orientation (0,0,0,1,1) for the same diagnostic residues.
It does not claim that denominator clears the two scaled rows or
that all five primes are in the stronger sample's ray.

## Why the arithmetic certificates prove exactness

Each terminal primality tree starts at 2. For a proposed prime n, the
certificate gives the complete recursively certified prime factorization
of n−1 and an a with a^(n−1)=1 mod n, and
gcd(a^((n−1)/q)−1,n)=1 for each prime q|n−1. Thus for every prime
divisor l of n, the order of a mod l is exactly n−1 (otherwise it divides
(n−1)/q for some q). Hence l≥n, proving n prime. This argument and the
verifier do not rely on a probable-prime flag, trace estimate or CM count.
It also certifies every prime factor used in the order drops.

For each curve the independently replayed Jacobian scalar multiplication
checks [N]R=O and [N/q]R≠O for every prime q|N, with the full factorization
of N and the affine drop coordinates. Thus the order is exactly N.
Discovery used candidate traces, integer factoring, and affine addition;
those operations need not be trusted for verification.

**Written comparison to the prescribed p-adic quotient (not a Lean
acceptance).** At the Hensel lift of each explicitly listed root r
(derivative 2r nonzero), (3−r) is a p-adic unit since a root reducing
to 3 would force p|7. The discriminant 64(3−r)^6 is a unit. For this
good integral Weierstrass model the reduction map to the smooth special
fiber is a group homomorphism; see [Milne, Elliptic Curves, 2nd ed.,
§4, Theorem 4.1(b), p. 63](https://jmilne.org/math/Books/EC2.pdf).
Its kernel is exactly the source's formal subgroup. Indeed an affine
point with v(x)≥0 has v(y)≥0 and reduces affinely. If v(x)=−k<0 the
cubic term dominates the linear term, so v(y)=−3k/2 and k must be even.
Multiplying [x:y:1] by p^(3k/2) gives normalized reduction [0:unit:0].
Together with O this is precisely the carrier
Q=0 or |Q.xRep 0|_p>1 in AlgebraicFormalSubgroup318. The quotient thus
injects into the residue group, and the embedded global R reduces to
the precise point (1+r,2r) used here. Its order there equals its order
in the quotient. Surjectivity is not needed. This matches the mathematical
objects of SelectedQuotientOrders318.order and does not claim any
newly elaborated declaration or identify unsupplied signs without Hensel.

## Reproduction and provenance

Run `python -B verify.py` and compare with FINITE-REPLAY.json. The checker
uses only Python's standard library. SHARED-CLEARING-ROW.json isolates
the valid five-member evaluation; SHARED-COVERAGE.json extends checking
to every prime position in that same grid and identifies all nonprimes.
All finite evidence is separable from the p-adic group-homomorphism
theorem. No CI or local Lean run occurred.

Sources inspected on a0950ac7: CoherentMultipleCharts318.u, chartU,
fixedRoot and chartU_negative; FixedDetectorScales318.product and
normProduct; ThreeDetectorUniformFamily318.c₁/c₂; ContactPrimeForms318
and ClearedContactForms318; MergedContactPrimePattern318.Values/product;
SelectedQuotientOrders318.order, and the foundation copy of
AlgebraicFormalSubgroup318.mem_formalSubgroup. The earlier
forward-original-order-parity-graph-r1 packet checked four independent
primes and explicitly disclaimed row completion. Its finite orientation
theory is prior work. These computations add linked five-position results,
not all-position success or an original-source proof.
