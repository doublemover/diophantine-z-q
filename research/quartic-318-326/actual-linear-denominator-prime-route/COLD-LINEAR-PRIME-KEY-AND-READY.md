# Independent cold receipt: original linear denominator-prime route

**Reviewed immutable author text:** LINEAR-GAUSSIAN-PRIMES-TO-ORIGINAL-READY-POLES.md,
SHA-256 29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0;
author manifest 236f9635865a5c6a2a2bba06c19e15921c7abb94be3e13cd683c2cc7a1fe20f4.
Reviewed quantitative union consumer A4-SIEVE-FOR-PRIME-STEP.md
c30ce02259b5f143d67dd289418b2a35a51bef1dd7234f70a2f2b1e967fd07e4.
The reviewer authored the A4 upper, not the linear lower/Ready
alternative. This receipt independently checks the NEW lower and
its join to that exact upper. No native Lean acceptance or
unconditional rational-point/rank claim is implied.

## Verdict

**Paper PASS on the common positive prime key, with original
local preparation and the full fixed Gaussian ray construction
as named inputs.** I found no missing nonlinear estimate, no
rank-six count, and no unwanted uniformity in a moving field.
The local order-only extension checks against the old source
formulae below. The conditional rank/point/page-287 work is
outside this claim. To avoid a symbol collision, let q_* denote
the new denominator prime; the fixed rational input of the old
witness stays unchanged.

## Fixed base and exact ray mass

1. Fix the true coefficients C_i=k_i Q² and all exceptional primes
   before s. The five root factors are monic by the exact
   ContactWeightWitness318.contact product, including root 0
   (so u is among the observed prime values). Q is chosen
   divisible by the BASE conductor F₀; enlarging Q further at
   the finite original denominator primes does not change
   either the prepared continuity class or the linear rank.
   Only afterwards choose tau>0 with fixed real/height margins.
   The affine forms have gradients (1,C_i) and (0,1), so all
   pairwise determinants are nonzero after merging repeated
   contact positions. On [3N/4,7N/8]×[tau N,2tau N] their
   values are genuinely positive and at most N, with q_*≥tau N.
   The volume is tau N²/8. The contact spacing is at least
   Q² tau N, much larger than the same-position and cross-position
   errors 1+2 sqrt N.

2. With M=16 times the chosen odd prime product, the prior
   exact norm-Artin group proof gives maximal rational-abelian
   subfield Q(zeta_(2M)), hence F_s=2M here (not a discriminant).
   This is the mathematical result in
   EXACT-GAUSSIAN-ABELIAN-CONDUCTOR-AND-ORBIT.md, with the
   two-sided cyclotomic proof. On the fixed base: (9,0) mod
   16 has norm 17 mod 32; (1,3) mod 7 has norm 3 and
   adjacent norms 2 and 6 there; (0,1) at other odd base
   primes has norm 1 and adjacent norms 2. These are all
   units where needed, and 17 mod 32 is 1 mod 8. In particular
   q_* and u in this same base norm class are 1 mod 408.
   The base residue's conjugate ray class differs at 7, and
   no unit corrects this difference: both are 9 mod 16
   so the correcting diagonal Gaussian unit would be 1.
   Since all C_i vanish modulo F₀, the simultaneous base
   cell u=q_*=b₀ mod F₀ is admissible. This is the necessary
   replacement of the old quadratic v=0 witness; no q_*=0
   residue is used. Its mass is one fixed positive constant.

3. Over Q(i), the ray group is the finite Gaussian unit
   ring modulo diagonal Gaussian units. Project the new ray
   group to the base group and to the new odd local norms;
   this is surjective by CRT and finite-field norm surjectivity.
   Kernel is the product of the new norm-one groups, each
   embedded using identity at the base (a diagonal unit with
   identity base residue is identity). Each new norm-one group
   lies in the full rational commutator via x/bar(x), by
   finite Hilbert 90 or the split formula. The rational
   commutator projects onto the base commutator; its kernel
   at the base is exactly the said product, because all
   commutators have trivial new local norms. Thus
   |G'_s|=|G'_0|∏_(ell new)(ell−chi₄(ell)).
   This proves actual independent variation in an abelian
   fibre, not independence of incompatible labels of a
   fixed Gaussian representative.

4. For a unit norm t at a new prime ell, split coordinates
   xy=t have ell−1 points; a zero translated norm is
   x=±1 or y=±1 and removes at most four points. Inert:
   a translated norm zero forces the Gaussian number itself
   to be ±1, removing at most two out of ell+1. In the chosen
   base orientation the representatives are injectively
   counted modulo diagonal units. Distinct choices have
   disjoint rational conjugate orbits of size two because
   their conjugates have the other base orbit member.
   Thus at each compatible abelian unit residue the exact
   accepted conditional fraction is

      μ_s = [2/|G'_0|] · ∏_(ell new)
                  safe_ell(t mod ell)/(ell−chi₄(ell)).

   On an incompatible base or nonunit residue it is zero.
   No factor |G_s| is independently charged for each form.

## Primary affine theorem and same-key margin

I reread [Frei–Tinková arXiv:2408.17441v3, §1.2](https://arxiv.org/html/2408.17441v3#S1.SS2),
specifically (1.9), (1.10), (1.14), Thm 1.4, (1.15).
It is the unconditional prescribed Artin-symbol theorem,
not the conditional result on primitive roots. Fixed integer
linear coefficients bound the stated complexity/size.
The sampled rectangle is convex inside [-N,N]^2, all
outputs are positive, and its Lebesgue volume is as above.
At fixed s the union of conjugacy classes is finite; expand
the product into class tuples and sum Thm 1.4. Distinct classes
are disjoint on any one unramified prime. Hence each rational
key is weighted exactly once by the log product (no count of
two split ideals). When D_K=F_s, the formula is precisely
F_s sum_C η=(F_s/φ(F_s)) μ_s: the compositum identity
[K_s(ζ_Fs):Q]=|G'_s| φ(F_s) gives this equality and removes
any possible extra group-order normalization.

The physical finite CRT main factor splits by the fixed base
and the new primes, since modulus F_s is their exact coprime
product. Outside the fixed base, distinct homogeneous zero
lines meet only at origin, so the common unit probability is
1−r/p+(r−1)/p². Select the fixed base to contain all
degeneracies and p≤4r. After multiplying by (1−1/p)^(-r)
the ordinary factors are positive 1+O_r(p^-2), with product bounded
below uniformly when grouped between new and outside primes.
The additional new angular factors are bounded below by
∏(1−4/(p−chi₄(p)))^r ≥ (log(s+2))^-C ≳ s^-1/2
for fixed r/base; can use the elementary Euler/Chebyshev
bound from the A4 note or the fixed prime harmonic bound.
One fixed base cell is enough at the BASE; do not use one
cell modulo the entire F_s (that would lose uniformity in s).
The prime-power correction O(N^(3/2) log^(r+1)N) holds by
fixed nonzero linear gradient on one coordinate and fixed
number of forms. It is negligible compared with tau N²/sqrt(s)
at fixed s.

The exact A4 note removes odd common adjacent primes above s
on the same finite selectors. Medium weighted bound
A N²/(s log s)+o(N²) is independent of tau in its coefficient;
the author note uses the weaker A N²/s, also sufficient.
Since tau is fixed first, either is o(tau N²/sqrt(s)) as an
s-choice inequality. Choose s after tau,Q and before N; FT is
applied with class field fixed at this s, only then take N
large. Large upper N^(2−1/40) polylog N and all error terms
are o(N²) at fixed s. The large part and the inclusive medium
cover every odd prime greater than s. Small primes are absent
by the true full ray representative. Each residual weighted
term is positive iff all original required prime rails remain;
one key survives. At a≡9,b≡0 mod16, v₂ Norm(π−1)=6 and
v₂ Norm(π+1)=2, so the remaining directed gcd is exactly 4,
not a further congruence-class average.

## Order-only denominator and Ready handoff (source-scoped check)

I checked the exact author hashes in local archived source for
ThreeDetectorCRTWitness318 (837caa15), PreparedIntegerSource318
(e3ecec83), SourceLocalProgression318 (cd5f09f0), 
ActualAlternateRatioPrecision318 (48606002),
ActualSourceRatioParameters318 (d670034b),
ActualPrimaryLogPrecision318 (d2c6bc48),
ActualDetectorFold318 (1bb3b85f), ThreeDetectorArithmetic318
(6afbbd9c). Also read the related literal SelectedFormalEntry318,
CompressedChartDomains318, ActualPadeRatios318,
ContactWeightWitness318 and PoleInputWitness318. This is a paper
transport of the actual statements, not a replay of a square-key
wrapper.

* The prime lcm CRT uses q_* in M_-,M_+, but not Π. Hence
  M_-|h, M_+|(h−1) give the original half-point formal
  near(1) membership at the appropriate two oriented places at
  q_*; no q_*^3 is needed for this argument. At all contact
  primes the old Π³ depth lemma is unchanged. The other arm
  reduces to the fixed ±R and ±n_j R by the same reduction map.
  β polynomials and rationals use actual generated chart
  values, not approximate n_j placed as witnesses.
* The five CRT compatibilities are indeed the old theorem's:
  gcd(M_-,M_+)=1, gcd(M_+,L)=1, gcd(M_-,L)=16,
  gcd(Π,L)=1 and gcd(Π,M_+)=1. For the last, a contact
  prime p_i can only divide a contact plus norm if equal to it,
  by the common [0.7N,0.95N] band and neighbor O(sqrt N).
  Different contacts unequal by spacing, same contact unequal
  by evenness. The plus norm for q_* is smaller than all contact
  primes. Do not add the spurious requirement q_*∤M_+.
  h₀ and L divisible by 64 imply the actual h₀ compatibility
  with gcd 16. ThreeDetectorCRTWitness318 takes arbitrary rational
  t and these data, so the old real interval and positive
  poles are obtained at the same index h>1.
* Formal primary ratio at q_* really can use depth1:
  ActualPrimaryLogPrecision318.original_ratio has arbitrary
  R≥1. At q_* the fixed alternate formula has depth1 input
  exactly, in its proper orientation. On their nonformal
  sides the denominators are chart values at finitely many
  fixed nonzero multiples; chart U,V, QJ, and the common
  alternate denominator are nonzero in the number field by
  the cited domain lemmas (the common expression at h=2
  yields the h−1=1 case; sign follows U odd and V even).
  Exclude both embedded norms of those fixed denominators
  and fixed primes where the chart or the half point lacks
  good reduction. For the ratio denominators at q_* this is
  a fixed exception list, not a condition selected after h.
* The literal trace uses the actual chain mod q_*, not a
  surrogate parameter square. All unweighted leaves lie
  in valuation ring from chart/ratio integrality on BOTH
  embeddings and rational coefficient extraction when 2
  is invertible. At q_*: v(T)=v(T−1)=−1, v(F(T))=−5,
  so v(W1,W2,W3)=(3,3,3) from W1=(T−1)^2/F(T),
  W2=W1^7(T−1)^18, W3=W1^25(T−1)^72. Every
  weighted addend in the actual 16 leaves has positive
  valuation. Fold starts at 1 and stays 1 mod q_* at both
  embeddings. Then rational real part≡1 and imag≡0
  (2,sqrt2 units), and trace quotient≡1/2 is a unit.
  Thus literal b has q_* valuation −5−6(−1)=+1.
  At fixed denominator primes v(T) is strictly low
  even by fixed Q saturation and the leading contact
  polynomial is the exact monic product; remaining
  primes have valuation zero of this factor unless
  one of the selected contact primes, already positive.
  Thus denominator parity really concerns the same poles.
* At p=2,3,17 approximate the p-adic square root of q_* by
  integers m and set d=DQm. The required exact old normalized
  factors u+k_{ji} Q² m² are integers, congruent to the
  square unit u at the relevant initial precision. Increase
  fixed Q at these primes enough to preserve all depth
  hypotheses. They are nonzero for approximants close to
  the target nonzero contact prime. Prepared's quantifier
  really accepts these u,d and the same h mod L, and has
  no real condition on the approximants; the target's
  real compact domain ensures all rational denominators
  nonzero, hence p-adic continuity at the target.
  The local closedness conclusion uses the valuation norm
  BALL, not assigning the Lean finite padicValRat value
  at zero: the target is nonzero by real positivity.

Scope boundary: this is not the old square-key Pattern and does
not automatically feed opaque old wrappers that require a globally
square t denominator. The genuine new result is common-key paper
existence and the matched original Ready inputs, conditional only
on the indicated original source preparation/local group ingredients
and standard CFT/FT theorems. No 318/326 rational points or quartic
conclusion were established by this review.

Signed: High Descent independent lower/Ready cold review, 2026-11-21 UTC.
