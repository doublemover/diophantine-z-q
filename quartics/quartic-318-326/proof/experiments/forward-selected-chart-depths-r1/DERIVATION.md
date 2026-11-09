# Actual half-point quotient orders and selected chart depths

## Historical source and exact boundary

Read COMPLETENESS-ASSEMBLY.md sections5–7 and PRIME-PATTERN-AUDIT.md, together with CompactLocalPointCoding318.finite_formal_quotient, FormalPoleCoherentChart318.actual_chart, ActualSplitOrbitEntry318.positive_depth/coefficient_bound, ValuativeOrbitMultiples318.prime_power_multiples/near_int and the pinned Mathlib finite-order/quotient/Nat.ModEq declarations recorded in SELECTED-ORDER-APIS.json.

The historical section6 already gives the half-point 2-descent argument, Gaussian rays and the required d±/4 order comparison. The present formal work incorporates the downstream actual local-order-to-chart implication. It does not replace the half-point comparison with membership of the doubled point or claim the Gaussian comparison has been formalized. The analytic ray/order-production boundary remains open.

## Actual objects and quotient order

At p with a genuine rho²=2 in Qp, use the exact embedding K→Qp and the original curve coefficient D. Entry means that the base change of M•R, for the original global half point R, lies in the existing algebraic formal subgroup on that exact elliptic curve. The subgroup has the original norm and integral coefficient proof.

Properness of Qp and the already constructed compact affine coding imply finiteness of the whole quotient by this subgroup. The quotient generator is the image of the base-changed R. Its additive order is positive. The pinned order-divisibility theorem says that any M divisible by this order kills this same class. Quotient zero is equivalent to actual subgroup membership. Both additive maps preserve integer multiples, including the conversion between a natural M and its integer cast. No number of curve points, finite reduction model or Gaussian order is inferred from quotient finiteness alone.

## Oriented chart and the actual CRT indices

FormalPoleCoherentChart.actual_chart consumes the actual M•R and returns strict smallness of chartU(M) and chartV(M)−1. The discrete actual valuation turns this into Near1. This selects the positive branch through the original duplication formulas, rather than choosing a root after the fact.

At a selected p dividing the actual merged product Pi, p³Mminus divides Pi³Mminus. The original primary congruence thus writes h=p³Mminus*m. For every signed n, the exact index identity n*h=p³Mminus*(n*m) permits the original prime-power multiple theorem to give Near4. The opposite congruence h=1 modMplus gives the INTEGER divisibility Mplus|(h−1), by the pinned Nat.ModEq theorem with its actual b−a direction. Every signed n then has Near1 at n*(h−1). No extra p-power factor is imposed on the opposite congruence. Indices zero and identity multiples are included.

## Fourfold delta improvement

For any field additive valuation, suppose y²=1−D*u⁴, D integral, v(2)=0 and Near_r(u,y) with r≥1. Then v(y−1)>0 and v(y+1)=v((y−1)+2)=0 by distinct valuations. The exact factorization (y−1)(y+1)=−D*u⁴ gives v(y−1)≥4r. The proof uses WithTop inequalities and allows u=0 or y−1=0, rather than dividing by a possibly zero term. At the actual selected p≥3, the rational integer2 is a unit at both conjugate embeddings. Apply the same literal chart-curve equation to obtain primary u/delta depths4/16 and opposite depths1/4.

## Every actual selected position, same h

AllSelectedChartDepths.OrderData quantifies over Fin3×Fin5 with p=natAbs(row(j,i)), where row is the literal cleared integer contact. Values already proves each p prime. OrderData adds p≥3, an actual rho²=2, and divisibility of the two actual half-point quotient orders into Mminus and Mplus. It does not include a coordinate-depth or branch premise.

The actual selected_divides theorem places every one of these primes in Pi, including positions repeated across rows. The final actual_depths theorem consumes the same two congruences on one h and applies the construction at every position and every signed label. Thus no independently selected local h, replacement point, root sign or unrelated order is introduced.

## Remaining joins and validation scope

The resulting bounds are the exact primary/opposite chart inputs for the next selected-contact argument. They do not yet prove the high Padé-ratio comparison errors, the complete weighted16-leaf trace hypotheses, the fixed-prime avoidance/unit conditions, Gaussian order divisibility, prime-pattern existence, rational Realizations or the rational anchor local-global principle. The unchanged172 consumer keeps these explicit; this packet makes no full arithmetic theorem claim.

172 predecessor sources are exact copies of172r2, including its narrow NormalizedOvalIndependence CI repair. Four new sources use finite1M budgets. The checker verifies exact polynomial factorization, odd-prime valuation examples including signs, primary/opposite index identities, finite cyclic order controls, literal source and index coverage, and all predecessor hashes. These checks and static dependency closure are source preparation, not kernel proof. No local Lean was run; hosted checking and distinct bounded review are pending.
