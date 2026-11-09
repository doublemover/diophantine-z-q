# Gaussian output to the actual same-index source witness

## History and source identity

Read the complete PRIME-PATTERN-AUDIT.md and COMPLETENESS-ASSEMBLY.md, especially their exact Gaussian ray/order and final CRT sections. The historical proof already contains the norm parity, cross-order gcd, finite order separation and CRT arguments. This packet incorporates their finite arithmetic consequences into the same original source/real-region chain; it does not claim those connections were absent historically. OrderSeparation and PrimeCRTAssembly are consumed through their full actual bodies, not only their theorem names.

## 1. Signed neighboring norms

For any signed a≡9 mod16 and b≡0 mod16, write a=9+16A and b=16B. The actual neighboring norms are

Nminus=(a−1)²+b²=64((1+2A)²+4B²),
Nplus=(a+1)²+b²=4((5+8A)²+64B²).

Both parenthesized integer factors are nonnegative and odd, hence strictly positive natural numbers. The code constructs them through toNat with the explicit nonnegative cast equality. Thus Nminus/4=16×odd, Nplus/4=odd and both quarters are positive. No positivity of a or b is assumed, and no truncated natural subtraction is used for a−1.

If Nminus at one position and Nplus at another have gcd4, the exact Nat.gcd_mul_left identity removes their common factor4 and proves the two quarters coprime. This is applied at every pair of original Fin3×Fin5 positions, including repetitions. The all-position LCMs divide the corresponding products; product coprimality therefore proves LCM coprimality.

## 2. Exact continuity gcd and finite avoidance

Avoid L a b retains the analytic Gaussian output that no odd prime divisor of the prior L divides either full neighboring norm. It is a concrete arithmetic input, not asserted to follow from the mod16 ray alone. For each odd factor above, a common prime divisor with L is impossible: the prime2 contradicts oddness; any other prime would divide the corresponding full norm and violate Avoid.

Let O be the product of all primary odd factors. O is coprime to L. The primary quarter LCM divides16O and is itself divisible by16, since the original index set is nonempty. With64|L,16|L. The pinned gcd cancellation theorem gives gcd(16O,L)=16; divisibility in both directions yields gcd(Mminus,L)=16. The opposite quarter LCM is coprime to L by the same product argument. This computes the exact shared factor rather than assuming it.

## 3. Actual prime/order separation with duplicate positions

The prime product is indexed by the MERGED distinct integer coefficients, whereas the order LCM is indexed by all15 original positions. Their domains are not conflated. Positive source values have natural absolute value equal to their actual integer value. For distinct coefficients k,l, the literal difference is (k−l)w² and |k−l|≥1; therefore selected-prime spacing is at leastw².

For the norm/ray representation p=a²+b², the opposite full norm has exact error Nplus−p=1+2a. A common real E satisfying1+2|a|≤E bounds that error. The finite growth hypotheses E<w² and p_j+E<2p_i yield both separation and the required bound Nplus_j<2p_i. These finite inequalities are left for the actual analytic output to supply, not inferred from unquantified asymptotics.

If the merged coefficient equals the coefficient of a given original position, the two primes are equal. The opposite full norm is even and the prime is odd, so the diagonal OrderSeparation theorem excludes divisibility. Otherwise the exact w² spacing and error bound give the off-diagonal exclusion. This handles repeated positions correctly. The original PrimeCRTAssembly.product_coprime_lcm then proves Pi coprime to the opposite quarter LCM, because each quarter divides its own full norm. A fixed prime cutoff greater than the positive L separately gives Pi coprime to L.

## 4. Precise actual CM boundary

CMMatch explicitly asserts, at each chosen original local root, that the literal finite count of the original model is the primary neighboring norm and its opposite-root count is the opposite neighboring norm. It is not inferred merely from j=1728, from a Gaussian norm equation or from passing finite samples. It retains the actual root orientations, original coefficient(3−rho)² and original point-count definition.

Given CMMatch, congruence of the two LCM functions identifies the literal quarter-count moduli with the newly constructed Gaussian quarter LCMs. crt_data then DERIVES positivity, both selected-product coprimalities, cross-modulus coprimality, opposite/continuity coprimality and the exact shared16. The remaining inputs are Gaussian output, pairwise full-norm gcd4, odd-prime norm avoidance, cutoff and finite growth inequalities, plus CMMatch. There is no assumption of an already compatible final h.

## 5. Prior thresholds, then an actual common h

The final prepared_family first obtains a real threshold T from the actual ThreeDetectorCRTWitness.prepared_family, which uses the fixed compact coefficient region and all three uniform chain limits. It separately obtains the integer divisibility modulus Q from the exact three-pole local preparation family. Both precede u,w, their prime values and the final index h.

After the actual Gaussian prime data, chosen orientations, CMMatch and finite separation/gcd inputs arrive, crt_data supplies all original mixed-CRT premises. For the same actual parameter≥T, the existing compact real-region theorem constructs h beyond any requested bound and beyond1. It retains h≡0 modPi³Mminus, h≡1 modMplus and h≡h0 modL, the original scalar margin and all four strict guard margins. Those strict margins produce the original nonzero guards; the Gaussian-ray preparation consumer then supplies Prepared at the same a,labels,h,parameter and actual stored poles190/241/292.

The result also retains the same input coordinate, every nonpole source row, all three real intervals0<b<17, and the globally fixed emitted roots. Given actual PointPairs at precisely those three stored b values, the existing certificate fill completes the first263 rows without changing those b values. The fourth scalar Realization and the global rational anchor remain separate in the full288 chain. No rational point or row hypothesis is silently substituted for a producer.

## Validation and remaining scope

Exact checks cover992 signed norm decompositions,2669 gcd-four/quarter cases,126 continuity-LCM examples,360 duplicate-aware spacing instances and a literal three-residue CRT example with the incompatible-modulus negative control. Six original finite curves under the additional historical mod7 Gaussian ray have the expected unordered norm counts, checked by direct finite field point counting; these examples are NOT a universal CM proof. All217 predecessor bytes and their inherited checks remain exact.

Source-policy/dependency closure is222 modules/222 baseline dependencies, with only OrderSeparation newly added. New modules retain the finite1M budget and proof-only section inputs explicitly. Hosted elaboration/recursive audit and distinct bounded source review remain separate; no local Lean compilation is run. Actual analytic prime-pattern existence, the exact CMMatch producer, four rational Realizations and the rational-anchor local-global implication are not discharged.
