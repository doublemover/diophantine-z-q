# Exact lower bounds for the actual q₀=1199923 test field and its raw input

Keep the exact compressed δ=1−βc²=H/Z² of the fixed a=0 specialization, with reduced c=C/Z, H=Z²−βC², and θ the positive squarefree class of δ. These calculations bound the input, not the result of the class-group test. No production q₀ or paired mod-13 nonvanishing is proved.

## True θ scan through 200,000,000

For an odd p dividing θ, outside β, the valuation v_p(δ) must be positive and odd: a pole of c gives a negative **even** δ valuation, and at a β prime c is integral and δ a unit. Thus any such p satisfies βc²=1 mod p, in particular (β/p)=1. The attached cpp scanner checks all p with this necessary sign outside the small/fixed places. It is the pinned earlier exact scalar calculator `find_alt_discriminant_primes.cpp` (588e265edc77a7e4f3f72a7ee846d8f041c714525a006be7a9b2ccd8ec1248fe; mathematical source 84065756…) with only the support filter changed from (3β/p) to (β/p) and the hit test changed from the alternate C/L' roots to D=βc²=1.

The original verified finite-order and valuation guards remain: each proposed finite annihilator is checked before use on the actual point at each completion; all finite scalar operations use exact arithmetic; at an h-chart zero the exact formal ratio U(i)/U(h) is computed with m=i/h (sign determined by the two-torsion reduction). At an h-pole with either two poles or no crossed cancellation, the CM i-pole bound and exact negative valuation arguments exclude c becoming integral, hence exclude θ. Code counts any unproved cancellation as inaccessible, never as rejection. For p≤200M all quantities in the signed 64-bit bounds fit (p², twice p², or the same-scale CM integer arithmetic; modular multipliers use uint128 where separately needed). The starting split calculation, inherited from the exact prior implementation, rounds an approximate square root and then verifies the result in integer arithmetic.

The outputs are exact:
```
11…30,000,000       relevant 928471  resolved 928467  formal 4912  excluded poles  4  inaccessible 0 bad order 0  hits 4
30,000,001…200M    relevant 4613546  resolved 4613535 formal 4616  excluded poles 11  inaccessible 0 bad order 0  hits 0
```
The four hits are exactly 131, 6551, 2470991, 16782959, each already proved valuation one in the original frozen controls. Additional exceptions omitted from the generic scan are accounted for: 2 and 3 are units; primes of R lie in the already treated 2/β support; at the four normalizer primes c has a pole (actual nonzero W units checked in the earlier normalizer receipt referenced by 84065756…). At p=7 the exact standalone check below gives δ=6. No inaccessible candidate in the scanned range remains.

At 7, the root √2=3 gives an additive reduction (v_7(d)=1 from (3−√2)(3+√2)=7) on the minimal model; its actual residue generator in the smooth locus has order 7. The other root √2=4 gives good reduction and the point has order 4. On the additive branch h≡i≡4 mod7, yielding the actual smooth (2,6), with U≡3. On the good branch both indices kill the residue and have nonzero formal lifts, with m≡1 mod7, so the unit chart ratio is 1 there as well as on the additive branch. Hence H_chart≡0, f≡1, N≡4, Q≡6, W≡5, c≡1, δ≡6 mod7. The check `check_theta_exceptional_places.py` enumerates both actual residue cycles and verifies this arithmetic.

The known factor product is 35,589,230,039,008,870,789≡13 mod24, whereas θ≡1 mod24. Therefore some unseen prime occurs, and every unseen prime is **strictly greater** than 200,000,000. In particular
```
θ ≥ 7117846043391004196808870789  (at least 93 bits),
|Disc(Q(sqrt(−1199923δ)))| = 1199923 θ
  ≥ 8540867177923863928847490663749247   (at least 113 bits).
```
There is still no assertion that exactly one unseen prime remains, nor any upper bound on their count from this scan.

## A different bound: literal reduced numerator has at least 207,779 bits

This part does **not** infer a similar lower bound on θ or on a maximal-order discriminant. It measures one exact raw defining coefficient.

At 3, the actual source curve is good over Q₃(√2) (unramified quadratic), the residue order of R₀ is 4, and the literal h is divisible by 4. Thus [h]R₀ is formal. The scalar multiplier m=i/h is a positive integer, with
```
v₃(m)=v₃(6¹⁵·3⁶⁵⁵³⁶·J)−v₃(h)=65547 .
```
For a nonzero formal point P at an unramified odd place, multiplication by an integer m increases the valuation of its formal parameter by at least v₃(m): factor out the unit part and iterate [3], whose linear term is 3z and whose higher integral terms have at least one higher valuation. Since U=−2z+O(z²) at O, the scalar Q=Nm(U([i]R₀)/U([h]R₀))/R_input¹⁵ has valuation at least 131094, R_input being a 3-unit. Thus for K=262188 one has the **actual** W≡N(h)² mod3^K; this ignores no surviving term of the literal scalar. Computing U([h]R₀) by binary chord arithmetic on 79-bit h suffices for δ mod3^K; the huge translated point is never materialized.

The GMP checker keeps coefficient balls 3^e(a+b√2)+O(3^N) and limits every operation to justified precision. Inversion uses the norm of a residual unit, which is a unit in this unramified degree-two extension. Starting at absolute precision K+512, the final U ball has absolute precision K+424, enough for the given integer residue (computed valuation 5). On that residue use exact rational reconstruction, not an estimate: let M=3^K, a=δ mod M and B=floor(sqrt((M−1)/2)). If 0<H<Z²≤B then ab−H=kM with b=Z² and gcd(H,b)=1. This implies gcd(k,b)=1 and
```
|a/M−k/b| = H/(Mb) < 1/(2 b²),
```
so k/b is a continued-fraction convergent of a/M. Enumerate all such convergents with denominator ≤B, using signed Euclidean remainders for the would-be numerator H. Require reduced square denominator, positive H < b, and 9H>8b (the exact established real margin); all are necessary for δ. Here H/Z² is reduced because gcd(C,Z)=1 and every β prime is a place of c-integrality. The bounded reconstruction at full K checks 121,065 convergents and finds no compatible one (there is only one positive bounded remainder). Thus Z²>B and H>(8/9)B. The lower integer floor(8B/9)+1 has bit length 207,779. A 4096-depth control with the same circuit and algorithm gives 3,246 bits. Full run took about 13 seconds of CPU time with GMP; execution-time is not a theorem bound.

Replays:
```sh
g++ -std=c++17 -O3 scan_actual_odd_theta.cpp -o /tmp/actual-theta-scan
/tmp/actual-theta-scan 30000000 11 | cmp - SCAN-11-30000000.txt
/tmp/actual-theta-scan 200000000 30000001 | cmp - SCAN-30000001-200000000.txt
python3 -B check_theta_exceptional_places.py | cmp - EXACT-EXCLUDED-SMALL-PLACES-AND-SIZE.json
g++ -std=c++17 -O3 bound_actual_scalar_expanded_input.cpp -lgmpxx -lgmp -o /tmp/actual-input-bound
/tmp/actual-input-bound 4096 | cmp - ACTUAL-H-HEIGHT-BOUND-4K.txt
/tmp/actual-input-bound 262188 | cmp - ACTUAL-H-HEIGHT-BOUND-262K.txt
```
This lower bound on expanded H does not limit the possible cancellation of square factors, and there is no certified numerical computation of the actual field's 2-primary class group. Even an eventual arithmetic pass of q=1199923 would remain distinct from every mod-13 requirement.
