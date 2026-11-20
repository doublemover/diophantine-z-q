# Both fixed level-2544 reference theta coefficients are units

**Scope.** The two coefficient residues here belong to the genuine
mod-13 Brandt eigenline of the fixed F53 elliptic detector. They
calibrate the two-source shorter-index test; no production
coefficient or full linked-pole witness has been evaluated. The
assertion on an integral eigenvector is via the characteristic-zero
lift in the existing detector paper, not a numerical guess of the
integer coefficients of that lift.

## Exact prime-to-auxiliary geometry

[The sibling maximal-order note](../odd2544-max-orders-r1/ACTUAL-ODD2544-MAXIMAL-ORDERS.md) proves the literal
maximal order of the original y²=x³+1 and the general isogeny-conjugate
lattice criterion, initially using q=13. Use instead the genuine
q=29 prime-to-all-weights arrows here, because 13 divides one
auxiliary discriminant. The original exact field F53^28 in the
horizontal orbit calculation supplies all 29-torsion. The actual
kernel vectors (1,s) of the four normalized Vélu arrows use
s=11,4,2,0 for j=(28,21),(28,32),(46,0),(50,0) respectively.
The script independently tests the normalized Vélu point sum on
the same literal kernel and curve, and retains the fixed generator
coordinates in JSON. On E0[29] use the actual (P,ωP) basis:
ω²+ω+1 is irreducible mod 29. In its lifted unramified quadratic
module over Z/29², F is semilinear, multiplication by a unit u
followed by conjugation, with norm −53. One can choose any lift
of its measured residue with that norm: relative to a true lift
the ratio is 1+29w with trace-zero w, and the change of basis by
1−29w/2 produces it (using conjugation minus identity on w/2).
A lift exists already by the nonzero norm derivative at a unit.
Thus the exact same 11,22 and 21 congruences from the q=13
proof determine all actual maximal order lattices by HNF.

For each of the 416 exact marked addresses, the code applies
two further line-invariance congruences, modulo 16 and modulo
3 on the literal transported subgroup generators. The marked
Eichler order is exactly this suborder: via the actual
degree-29 map the torsion at 2 and 3 is genuinely identified,
and dividing maximal basis numerators by 29 does not
change line preservation. Each congruence is surjective on
the relevant local matrix algebra; the checks record index
16·3=48, hence reduced discriminant 2544. In all classes
the marked group of units modulo scalars is trivial: away
from j=0 it is already trivial, and at j=0 the extra
order-three automorphism cannot preserve the 16-generator
line (its reduction mod2 is irreducible). Thus all ST factors
t_x in (5.10) are 1. The exact same 416 addresses and the same
λ=[224]φ0 residues agree with the old unchanged detector,
including anti-Frobenius, not merely equality of unmarked j.
These new HNFs have no coefficient prime in their denominators.

## Coherent local weights for both fixed sources

Use [Sirolli–Tornaría §§4–6,8–9](https://arxiv.org/html/2107.04483).
For the normalized characteristic-zero newform g at level 2544
lifting the old F53 eigenline, the Atkin–Lehner signs are
W16=+, W3=−, W53=+ as in the previous detector. The two types
at (∞;2,3,53) are then
  gamma_−=(−;−,+,−), with l_−=146965; and
  gamma_+=(+;−,+,+), with l_+=−323.
The section 9 sign equation holds in each case. The auxiliary
l has the opposite symbol at the ramified prime 53 and the same
symbol at 2,3; the l-twist of g in each case is nonzero by the
genuine original reference CST product. The type-II prime 3
is needed for both; 53 is needed only for the negative D
source. There is no type II at 2 since W16=+. For these fixed
fundamental l and D the coefficient is the lattice sum of
disc(y)=lD in ST Prop. 5.1(5.2); the ideals a,b,c there are
all the unit ideal. The published extension past the initial
coprimality hypotheses is needed at the actual reference,
since l and D share 17,19. Referring to the final Theorem B
and Prop. 8.1 (not only the initial 6.3) handles it.

The adelic representative for each target has at 29 the
matrix carrying its enlarged Tate lattice back to the
original one (diag(29,1) in its kernel-adapted basis);
at 2,3 it carries the literal chosen line back to the
standard line by a determinant-one integral matrix (extend
a primitive generator to a determinant-one frame), and at every
other place it is 1. Thus R_x=x⁻¹ R x as in §3,
with the intended actual p53 orientation from the prime-to-p
Vélu identification, not the abstract unmarked order alone.
The global norm character in (4.13) is then (l/29) for
each degree-29 arrow and 1 initially. Here it is +1 for
both l. At the individual type-I primes (5,7,13,17,19
or 17,19) the representative is 1 and the order locally
equals the first maximal order. In its basis modulo scalars
(ω,γ,ωγ), the literal negative discriminant numerator is
  −9Δ(b,c,d)=3(3b+2c−d)²+4·53((c−2d)²−(c−2d)(2c−d)+(2c−d)²).
For q a type-I prime choose the lexicographically first
nonzero isotropic z mod q, then the unit character is the
Legendre symbol of minus the polarized Δ pairing, and
on the proportional isotropic line the Legendre symbol
of the multiplier. Inverting 9 and the denominator 29
is allowed at all these places. This is precisely §4.1; it
does not drop the sign of the bilinear polarization.

At 3 the two distinct diagonal entries in the marked
split residue ring are the eigenvalue on C3 and the
other eigenvalue. With z=diag(1,0) in the frame where C3
is first, the quotient <y,z>/<z,z> is their difference.
Therefore the type-II factor is its Legendre symbol at 3.
Changing the added complementary vector leaves the
difference unchanged. At 53 use z=ω and reduce y=A+B F
modulo the quaternion maximal ideal; A lies in F53²,
and the quotient reduces to the coefficient of ω in A,
namely (3b+2c−d)/(3·den) mod53 for the source lattice
numerator. Use the **odd quartic** character χ53 with
χ53(2)=i (2 is primitive mod53) and conjugate it as in
ST (4.5). Using the quadratic character here would be
incorrect because it is even. Both embeddings of the
constant i into F13 are retained: 5 or −5=8.
The two original global signs y→−y are handled by
the two odd weights as prescribed, not by halving a
lattice count. For l_−>0 one may keep the skew-holomorphic
coefficient and its absolute square; the standard §9
holomorphic identification just transports the index
|D| and does not rechoose the class-dependent weights.

## Calibration at the fixed reference

At m0=455, d0=323, the two target pairs (D,l) are
(146965,−323) and (−323,146965). Both lattice sums have
discriminant −47469695. The exact script enumerates
the five maximal-order root lattices once, tests the
same actual 16- and 3-line compatibilities on each
mark, and computes the two different prescribed
weight products. It accumulates literal integers using
the displayed 0,…,12 representatives of λ, so the sums
reported before reduction are representative-dependent,
not purported characteristic-zero complex sums.
It returns
  A_+(146965)=−3312 ≡3;
  A_−(323)=−3312 i, so its two conjugate residues are 2,11
in F13. They are all nonzero. Exact divisibility and
deterministic basis reduction use rational/integer arithmetic;
no float sqrt or numerical Hecke lift is used.

The actual lifted real quaternion vector F can be normalized
to reduce to λ: the actual simultaneous residual eigenspace
is one-dimensional, including the commuting W53/Frobenius
sign, so reducing a primitive vector for the lifted character
lands on this same line. The characteristic-zero eigenfield
and vector can be taken real by self-adjointness and the real
Hecke eigenvalues, before adjoining i for χ53. Complex
conjugation therefore acts on the displayed quartic field;
both entries are reduced at the same chosen local prime,
not at a second arbitrarily selected prime. The ST lattices
and weights are integral at that prime, and coefficient maps
are linear in this very F, so the computed residues are
the reductions of the actual reference coefficients.

By the previous [CST/ST paired ratio](../FIXED-LEVEL-ODD-RESIDUE-SHORTER-NORMS.md)
for the fixed m=455 and any d in its stated compatible family,
the square of the toric period P_d(F)
relative to P_{323}(F) equals the ratio of the product of the
two squared absolute theta coefficients. The genuine reference
period has residue 11 (or its simultaneous sign), whose square
is 4. The reference coefficient product has residue
3²·2·11=3 mod13. Thus on the **same** sign convention

    P_d(F)^2 = 10 A_+(455d)^2 A_−(d) conjugate(A_−(d))  (mod 13).

The nonzero test is equivalently that all three indicated
coefficient residues are units. This proven calibration is for the fixed m=455 only; the
[separate varying-field note](VARYING-CM-NORMALIZATION-ADDENDUM.md)
is conditional on a new identification of the actual test vector
and marked specialization, not part of this fixed-field result.
Here CCL/original multipliers
if present still require their own unit/comparison check.
This is a reference calibration, not one of the HUGE unknown
production coefficients. It retains the original rank and
marked-point proof boundaries. The general batch norm sieve
in the sibling paper applies to its fixed weighted lattice
inputs in principle without changing any sign convention.

Reproduction (the geometry step uses existing finite-field
owners plus SymPy HNF; the coefficient evaluator is stdlib):
  python actual_odd2544_marked_orders_q29.py
  python odd2544_reference_coefficients.py
