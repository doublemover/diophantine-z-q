# The fixed affine linear-q count, and the exact finite inverse

This is the original 318/326 forward lane, not frozen 617. It replaces the
entire signed Gaussian-key existence hypothesis by a narrower quantitative
producer. The old key/output definitions remain unchanged. There is no
native class-field, prime-pattern, sieve or rational-point claim.

## External input: three counts on the same signed rational carrier

Fix original nonzero labels, their Clearing C, L>0 and 64|L, Q0>0, and
real rational T. First choose Q0|Q with Q>0 and a fixed thin positive
rational τ. The actual time threshold follows once
max(T,0)·(D Q)²·2τ ≤ 1/2. Choose fixed positive A and fixed medium
constant D_med **before** the wheel cutoff s=m²; then for every
sufficiently large positive integer m, choose a scale B (equivalently
N=B², a cofinal subsequence) at this fixed m. Choose m² ≤ Y and a finite
set of distinct integer rational keys (u,q), with one genuine oriented
representative at each merged coefficient and at q, on the same key.
The thin rectangle in 29e54194… fits the explicitly weaker native
ranges, including p∈[N/2,N], q∈[τN,2τN] and 4q≤N.

At a fixed m, the lower needs a fixed-field Frei–Tinková v3 Thm 1.4
estimate, with actual fixed base and additional wheel moduli as in
29e54194… / peer 3cd4198d…. Genuine prime values, one sign family and
one weight per key are essential. The prime-log weight is exactly
log q times the product of log(u+kQ²q) over distinct contact k only.
Each actual oriented representative avoids each of the two neighboring
norm zeros separately at every odd prime p≤m². This is the same support
as the ray-class union, not a large-prime restriction; no uniformity
of the fixed-m theorem as m varies is required. Choosing the least
permitted oriented representative in a finite search for each true
key is sufficient. It does not change the weighted lower.

Let Hit(p) mean an odd p divides one directed minus norm and one directed
plus norm, where the positions may coincide. Let M_m,Y be the mass on
keys with m² < p ≤Y, and L_Y the mass on keys with p>Y. The named
output CountProducer says
  total ≥ A N²/m;
  M_m,Y ≤ D_med N²/m² + E;
  L_Y ≤ G;
  E,G ≤ A N²/(4m).
It also records geometric windows, the explicitly fixed finite
cutoff horizon, and true norm/ray/prime data, but does not require
the cross gcd, any quarter bound, or an original index.

The independent A4 argument c30ce022… supplies these last two weighted
count estimates on the same genuine-prime carrier, by enlarging
each upper-bound problem to an ambient box after the injection. It
gives medium O(N²/(m² log(m²))) + an o(N²) at fixed m and large
O(N² log^r(N)/Y). We take Y=floor(B^(1/20)) (after m), absorb the
log into a D_med N²/m² bound, and choose B to absorb both errors.
All finite coefficients and exceptional primes were fixed earlier.
The lower is at least A N²/m by the fixed-base positivity and the
wheel-product lower, with A allowed to depend on the fixed phase
including τ. No moving-field conclusion, old rank-five tail, or PET.

## Exact local finite factor

At an off-minors modulus p, write the images κ=kQ² as distinct
elements of F_p. With the true q form present, y=q mod p must be
nonzero. For each such y the forbidden x are exactly -κy, all
different. Thus the ordinary admissible pair count is
(p−1)(p−#contact slopes). Its true ordinary local factor is that
count divided by p² times (p/(p−1))^(1+#contact slopes). In particular
there is no extra q=0 fibre from the earlier quadratic route.

Norms on this support are units. In split coordinates xy=n, the
two translated norm-zero tests remove exactly candidate first
coordinates 1,-1,n,-n (collisions allowed, e.g. n=±1). At an inert
prime the two possible removed elements are ±1 themselves. For a
common norm-fibre size H=p−χ4(p), the native finite normalized mean
compares the conditional factor for r merged forms with
(1−bad/H)^r, bad=4 or 2 respectively. Identification of the rational
Chebotarev conditioned probability with this finite norm fibre
uses the independently reviewed ray field; it is not built into
this finite mean lemma. On the fixed base there is a different
positive factor, already described in 29e54194…, with u=q=b0
unit at that level (never q=0). This rules out a misleading
naive product over every prime without the base compatibility.
The same finite mean file records the exact ambient rank-four contribution
p³+p²−p from the two-norm count, before intersections, and the exact diagonal
opposite-event slice a=0,b²=−1.

## Entirely finite inverse and stopping point

1. Choose m once with 4 D_med < A m via the Archimedean property.
   The two upper masses sum to strictly less than the lower; the
   proof permits medium/large overlap (it is charged twice).
2. Select one key with no odd hit. At every requested position
   N_minus=64·odd and N_plus=4·odd by the actual mod-16 ray.
   With no odd common prime, gcd on each ordered pair is exactly
   four, even for repeated contact coefficients or the q position
   paired with itself. Each odd divisor of L lies in the original
   small wheel and was excluded individually before selection.
3. From p≤B² and p=a²+b², a≤B, so for B≥3,
   N_plus≤B²+1+2B<2B². Every contact ≥B²/2, hence every plus
   quarter is strictly below every contact prime, including the
   plus norm at q. All earlier numerical cutoffs follow by the
   same windows. The actual old rational t follows from the zero
   contact coefficient (=u) and the chosen thinness inequality.
4. Copy the unique selected sign data through the literal projection
   Option(Fin3×Fin5) → Option(merged coefficients); none is q.
   Exact old GaussianKey is constructed, and its existing inverse
   gives unchanged elliptic half orders, original CRT index, and
   the same Ready from ActualLinearQCountToReady318.integer.
   This does not prove/assume a rank, October two-converse or anchor.

The deterministic A4 injection uses two distinct genuine indices:
for contact i≠j the difference coefficient (i−j)Q² is nonzero;
q and any one contact equally determine (u,q). Therefore even a
same-position event is embedded using a distinct companion, not
a fictitious second orientation of that same prime. This is done
before absolute values or finite cube projection.

Native files and independent scope: FiniteExclusion (weighted
selection, explicit slack, gcd-four), FiniteRayMean (ordinary local
factor and split/inert refinements), TwoNormInject (actual affine
inverse), then FiniteKey and CountToReady (live original packet
ports). The 3-module Mathlib-only step is the early test candidate
after the existing fold smoke; the original native closure is still
source-only and larger. No local Lean or project actions were used.
