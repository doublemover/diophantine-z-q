# Exact orientation feasibility from inexact annihilators

**Theorem.** Fix any finite nonempty family of pairs of finite-order group
elements, Π,L>0 and an integer h0. The exact set of allowed orientations
for h≡0 mod Π³M−, h≡1 mod M+, h≡h0 mod L can be determined without
computing every order. Supply (1) one positive certified annihilator N_k
for each generator key, (2) an exact kill test `[a]P_k=0`, and (3) certified
factorizations only of the *overlap gcds* below. Private cofactors need
not be prime tested, factored or known to divide the true order. The
output also gives one valid witness or progression per feasible assignment;
its period can be strictly larger than the true minimal period.

### Inputs and repeated occurrences

Let n_k=ord(P_k), not supplied to the algorithm. Every occurrence retains
its own side in the original indexing, but may reference a common key
**only** when the entire underlying generator in the same group has been
identified, e.g. the same p and the same chosen reduction root. Equal
prime alone is not identification of opposite branches. Distinct keys
may be used unnecessarily; this is correct but may cost a larger gcd
factorization. If the same identified element has several certified
bounds their gcd also kills it; using one valid bound is sufficient.
The verifier tests N_k P_k=0 and tests P_k=0, replacing N_k by 1 for an
identity element. This last step is necessary for repeated keys whose
order is one.

### Algorithm and proof

1. For distinct keys k,j collect the prime divisors of gcd(N_k,N_j).
   Also collect those of gcd(N_k,Π) and gcd(N_k,L). The union S is finite.
   Only these gcds, not products or individual full N_k, need factoring.
2. Begin T_k=N_k. For each ℓ∈S repeatedly replace T_k by T_k/ℓ when
   integral and the quotient still kills P_k. Stop at the first failure.
   Since n_k divides every live T_k, the kill test passes exactly when
   vℓ(T_k)>vℓ(n_k). Thus each active prime exponent ends **exact**, other
   prime exponents remain untouched, and n_k|T_k.
3. Apply the earlier graph or generalized CRT solver with each occurrence
   bound T_k. No deduplication of original positions is necessary.

To prove step 3, fix an orientation and let m± be the LCMs of the true
orders and t± those of T. For ℓ|L, all occurrences which can have a
positive ℓ-valuation have exact ℓ-exponent by step 1. Therefore

    gcd(Π³m−,L)=gcd(Π³t−,L),    gcd(m+,L)=gcd(t+,L).

The same argument shows gcd(Π,m+)=gcd(Π,t+). For the cross-side
coprimality, a prime dividing bounds on different keys is active, hence
divides both corresponding true orders. If the same key appears on both
sides, its shared T is nontrivial exactly when its actual order is
nontrivial, by the identity check and n|T. Conversely n|T ensures every
true cross-side conflict persists. Thus gcd(m−,m+)=1 iff gcd(t−,t+)=1.
For repeated keys we assert **only coprimality equivalence**, not equality
of the numerical cross gcd. Combined with the Π condition, the three
residues using T satisfy exactly the same CRT existence criterion:

    gcd(Π³t−,t+)=1,  gcd(Π³t−,L)|h0,  gcd(t+,L)|(h0−1).

The original nonempty paired positions may be all 15, including repeated
primes; there is no common-divisor-at-all-positions assumption. A CRT
witness obtained with T automatically satisfies the original residues,
since n|T. The converse for individual h is false: for true minus/plus
3,7 and bound minus/plus 15,7, Π=L=1, h=36 is valid for the true orders
but not the bounds. We preserve existence, orientations and valid
witness construction, **not every h**, shortest periods, or exact
complete orders. Large overlap gcds can themselves be difficult; this is
not a worst-case polynomial factoring algorithm.

### Consequence on a genuine linked row

FIXTURE.json reuses the five linked prime values, both literal sign
branches and independently certified exact comparisons from the strong
model-label shared-clearing example in forward-linked-row-order-certificates-r1.
Its *input* annihilators are separate positive candidates; we check every
one by curve scalar multiplication. A CM trace guess is not an assumption
because an incorrect annihilator fails. The ten actual orders stored for
regression are **not** used by trim. In this example 154-bit annihilators
need only gcds at most 128 and tests at two active primes: **2 and 5**.
43 successive strip tests suffice. Three final bounds are strictly bigger
than the actual orders, yet the sole compatible orientation remains
(1,1,0,0,1) at L=16,h0=0 and the five-prime Π.

These are actual finite elliptic group operations, not arbitrary numerical
surrogates. The previous linked-row packet gave the exact good-reduction
kernel comparison for the Hensel lifts. No full fifteen-prime Values record,
new point-pair, real-guard congruence or Lean verification is asserted.

### Replay and historical comparison

Run `python -B verify.py` and compare FINITE-REPLAY.json. The standard-library
reference implementation uses an explicit factor-support oracle: its contract
requires **certified prime entries**. The fixture's small gcds are factored by
exhaustive trial division. A product of composite blocks labeled as primes
would not satisfy this interface. The diagnostic includes 400 random
15-position edge systems, 4,800 direct CRT comparisons, a separate exact
32,768-orientation example, identity and duplicate keys, and a 648-bit
private composite that the factoring oracle must never be asked to factor.
The proof is separate from these finite tests.

The earlier forward-original-order-parity-graph-r1 algorithm is already
factorization-free **after exact orders are supplied**. The new step begins
before those orders are known and proves when inexact bounds are a complete
substitute for feasibility and witness construction. It does not replace
earlier exact orders in any manuscript or Lean denominator theorem.
