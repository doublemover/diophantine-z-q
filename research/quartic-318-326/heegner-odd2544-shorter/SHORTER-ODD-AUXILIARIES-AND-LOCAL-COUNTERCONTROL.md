# Two shorter actual theta auxiliaries, and a matched local countercontrol

Same original p=53 reduction, mod-13 coefficient place, exact 416 oriented marked supersingular points and fixed real algebraic Hecke lift F as in the level-2544 reference. The two new weight systems reduce the constant work of the coefficient calculation. They do not solve the full prime support or select a production twist.

## Actual new auxiliary values and calibration

In the existing positive source with l=-323, the fundamental positive D=37 has the required ordinary local type (+;−,+,+) at (∞;2,3,53); its five actual class contributions are (44,60,−70,92,42), giving 12 mod13. Thus its actual classical central value for g⊗χ₃₇ is nonzero by Sirolli–Tornaría. Use the new fixed negative-source auxiliary l₋=37. In this source the fundamental D=−35 has the required (−;−,+,−) type, and the phase-normalized coefficient is 10 mod13 from (−16,120,16,56,−36). Thus L(g⊗χ₋₃₅,1)≠0, so choose the new fixed positive-source auxiliary l₊=−35. Both auxiliary tests are prior to the new calibration; there is no circular nonzero assumption.

For the exact two theta constructions use [Sirolli–Tornaría Proposition 5.1, 5.11, Theorem B, Proposition 8.1 and Section 9](https://arxiv.org/html/2107.04483). The new Type-I primes are {37} for the negative source and {5,7} for the positive. They are prime to the fixed q29 orientation transport and 48·53; use the same determinant-one local marked frames, same χ_l(29) transport rule, and the same Type-II character at 3 (both) and at 53 (negative only). Coinciding factors of D and l are covered by Theorem B/Proposition 8.1. This matters at +146965 for the new l₊, and is not an unstated coprimality assumption.

Keep the same genuine reference m=455,d=323 whose raw mod-13 period is 11. New weighted coefficient data are:
```
A₋^37(323) = 12 mod13  (phase-normalized, norm target 11951).
A₊^(−35)(146965) = 9 mod13  (norm target 5143775).
```
The negative source has type-II at 53. On each fixed signed discriminant row its Ω coefficient has exactly the two values ±T₀ modulo 53; removing the common quartic unit accounts for all terms in the combination. Conjugating uses the same F and chosen residue prime; the negative norm product therefore reduces to the square of the signed phase-normalized coefficient. This is the same mechanism as in the old independently checked reference, with new T₀ computed from lD. The reference square is 4 and (12·9)²≡3. Hence, for every m,d meeting the exact reviewed varying-CM requirements,
```
s(m,d)² = 10·(A₋^37(d)·A₊^(−35)(md))²  mod13.
```
The value 10 being unchanged is a calculation, not an assumption. Compared with the older auxiliary sources, the negative norm target shrinks by 146965/37≈3972 and the positive by 323/35≈9.23, equivalent to square-root reductions in the one-coordinate sieve. These are constant factors, not an asymptotic breakthrough.

## Exact zero and unit with the same required local types

Take the very same m=455 and d=1931 or 2579. Both d are actual primes, each 11 mod24 with (d/53)=−1 and (−455/d)=+1. Their Legendre symbols at (5,7,13,17,19,37,53) are identical, namely (+,−,−,−,−,+,−); this includes the discriminant primes of K and both original/new auxiliaries. Both positive coefficients are 11 mod13. But the negative coefficient is 0 and 1 respectively, so the squared raw residue is 0 and 1. These are genuine coefficient controls via the same oriented reference, not artificially assigned local weights. They show that these finite local sign and splitting conditions alone do not force a mod-13 detector, even with the other coefficient a unit. The zero is not a claim of vanishing over Q. Neither d is the fixed scalar's production index.

## Exact bounded acceleration and replay

```sh
g++ -O3 -std=c++20 rank3_exact_reps_small.cpp -o /tmp/rank3_exact_reps_small
export PYTHONPATH=../odd2544-weight-primefree-r1
python3 recalibrate_short_auxiliaries.py /tmp/rank3_exact_reps_small
python3 replay_short_controls.py /tmp/rank3_exact_reps_small
python3 check_negative_small.py /tmp/rank3_exact_reps_small bench
```
The C++ loop replaces only the bounded (x,y)-box search. Integer inequalities after a floating square-root seed certify each exact root and fork; the Python caller rechecks the genuine norm for every emitted lattice vector. The same q29 orders, 416 markings, Type-I and II weights, and raw λ labels are untouched. The exact old Python enumerator reproduced the new negative d1931 and2579 rows as well. Bounded equal-output CPU timings on this cloud instance for the *same old auxiliary* were 5.415s→0.809s at d83 and 26.151s→3.045s at d419 (6.69×, 8.59×). This demonstration only controls finite cases admitted by the C++ bounds. It does not turn a 76+ digit target into an evaluable one or assert a nonzero coefficient for that target.
