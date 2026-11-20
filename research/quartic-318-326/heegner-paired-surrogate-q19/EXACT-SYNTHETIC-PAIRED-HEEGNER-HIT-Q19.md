# Both raw mod-13 Heegner detectors hit at one exact surrogate prime

This is a true finite simultaneous calculation in the **same** 416 marked q29/p53 detector, for a small surrogate scalar. It is not the literal h,J production scalar, does not test its q=1199923, and proves no prime distribution or uniform forward rank theorem.

## One scalar, one auxiliary field, one prime

Let
```
β=17,  θ=409,  m=455,  q=19,
b=(408/62269)^2,
1−b/17=409·(3079/62269)^2 .
```
The last exact identity follows from 17·24²+409·3079²=62269². The scalar is genuinely positive, has square reduced denominator, is a rational square (hence square at 2,3,17), and is below 1/10000. Its prescribed positive squareclasses of 17b and 1−b/17 are exactly β and θ. It was not obtained from the fixed procedural h,J.

For β of support size one there are no I slots. The exact arithmetic checks are (q/17)=+ and (q/409)=−, with (17/409)=(409/17)=+. Thus the old K row is zero and the one-entry θ block is 1. Also q=19 mod24 and (q/53)=−, while β and θ both have square symbol at 53. Each of 17,19,409 splits in the same K=Q(√(−455)); m=23 mod24 and (m/53)=−. The same literal q occurs in both n=17q=323 and nθ=132107, which are both 11 mod24. One can take the exact same arithmetic prime progression q=19 modulo 4,024,118,280; the only assertion calculated here is at q=19.

## Four frozen coefficients, two actual period hits

Use the very same 416 marked order tables and normalized mod-13 eigenline as the exact prior calibration. On the fixed ST weights l₋=37, l₊=−35 (no new phase or integral vector), exact ternary norm enumeration and the marked weights give

| d | negative index | A₋ mod 13 | positive index | A₊ mod 13 | squared raw projection mod 13 |
|---:|---:|---:|---:|---:|---:|
| 323 | −323 | 12 | 146965 | 9 | 4 |
| 132107 | −132107 | 10 | 60108685 | 2 | 9 |

The two initial coefficient rows already form the original calibration; **both companion rows are new**, at one and the same q and m. The attached exact output stores all five signed lattice contributions and the phase root for each entry. For the companion the larger exact positive norm target is 2,103,803,975, not a scaled copy of the old target. For the fixed source and m the earlier reviewed calibration is the equality of conjugate products with the squared raw detector, constant 10. The packets have the same three local types at 2,3,53, the same split CM embeddings, and the same mark and reduction place. The negative phase uses its two conjugate factors, whose product reduces to the square of the signed table coefficient in this normalization. Thus the two raw unaveraged rational Heegner traces have nonzero 13-primary projections (their signs need not be chosen here). This computes through the exact calibrated theta equalities, not by tracing literal mixed lines for the companion.

To replay the exact four coefficient rows, use the already published shorter coefficient driver and the exact q29 book. From this new folder, set SHORT to the earlier heegner-odd2544-shorter directory and BOOK to the odd2544-weight-primefree-r1 directory containing the book and reference implementation. Verify their preserved source hashes, including book aa650e289ef886c824cf93414845c9586c12e5db0d640f6a6d48452ca9bb1a8e and reference implementation be160ba3f07261dda8f10aaec5f2196cef00b7d94e89fdc4c040cba2d06e660b. Then:
```sh
g++ -O3 -std=c++17 "$SHORT/rank3_exact_reps_small.cpp" -o /tmp/q19-paired-rank3
PYTHONPATH="$BOOK" python3 -B "$SHORT/recalibrate_short_auxiliaries.py" /tmp/q19-paired-rank3 -323 37 146965 -35 -132107 37 60108685 -35 | cmp - EXACT-TORIC-PAIR-Q19.json
python3 -B check_q19_paired_support.py | cmp - EXACT-Q19-PAIRED-SUPPORT-AND-SEL2.json
```

## Algebraic conclusion for this small example only

The actual raw unaveraged traces are rational by the existing pointed Fricke computation for E_d at full level 48d² with root sign −1; the Fricke relation permutes the appropriate class-indexed orbit and has no cusp shift for that based map. This is the same uniform Fricke formula used at the fixed calibration, now with the two tested d. Both d are good at 37, with #E_323(F₃₇)=32 and #E_132107(F₃₇)=44 by independent point counts in the arithmetic checker. Reduction at 37 injects rational 13-primary torsion, so neither curve has any such torsion. A rational torsion point of order prime to 13 could not have nonzero projection to a 13-primary group at 53. Thus both genuine raw traces are nontorsion; a later nonzero integer multiplier does not change this global fact, regardless of whether it itself is 13-adic unit.

For both curves, the standard full 2-descent in coordinates (x+3d,x−d) is the same as in the original simultaneous-realization lemma (V13 at 7845ff). The arithmetic checker enumerates the exact necessary linear equations for positive second coordinate using these two explicit support matrices. There are only four solutions in either case, with zero second-coordinate exponents and no factor of 3. The torsion pair (3,−d) has negative second coordinate, so the number of all-place classes is at most eight. Conversely (17,1) belongs to every local image: it is identity at 2 and infinity, equals the first torsion class at 3, and at a support place equals identity or the first torsion class according as the place lies away from or over 17 (all needed symbols above are exact). At every other odd good place it is unramified. It is independent of the two rational torsion classes (d,1) and (3,−d), as d contains q=19. Their span therefore gives eight actual local classes. Thus Sel₂ has size eight on both.

Since E_d has full rational 2-torsion, the Kummer sequence bounds its rational rank by one. Actual nontorsion then gives rank exactly one, and E_d(Q)/2 E_d(Q) already has size eight. The actual everywhere-local class (17,1) therefore comes from a rational point on each curve. It is not the class of 2-torsion; on those points the equation forces the nonzero x-coordinate to have squareclass 17. This obtains a genuine two-curve marked-point existence result for this explicit **surrogate**, with neither a reverse analytic theorem nor Sha-finiteness assumed. It does not give the point coordinates, handle any production scalar, or furnish a mod-13 theorem in the moving prime.
