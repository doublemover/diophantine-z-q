# PreparedIntegerSource318: exact cast order and original assignment alias

## Observed scope

Run43578868567 at977040de03da47698b89a3345d93e2ffcbc2220c verifies ScalarCompleteSource318 in both forward packets (38.776/52.569s). Weighted-r11 artifact14106844992 and descent-r11 artifact14108076675 independently first fail PreparedIntegerSource318 (2.321/2.522s). Exact own logs agree after only packet-name normalization. Errors are the rational/real strict lower-bound cast at line28 and failed matching of the original fill expression against local w at slots118,82/83,37,0/33/37 and145. Warnings alone are not separately repaired.

## Required input and constructed scalar comparison

ScalarPoleRealDomain318.pole_domain requires the original rational strict norm bound 1/100 < |normCoefficient(chartU h)|. The user of scalar_domain provides the exact real image inequality with the SAME threshold and norm. Instead of exact_mod_cast, the candidate applies Rat.cast_lt (K:=ℝ) in its reverse direction and normalizes exactly Rat.cast_div, cast_one, cast_ofNat and cast_abs. The rational order embedding reflects the original strict inequality; it does not weaken it, change100, remove absolute value, assume a rational premise or infer it from positivity. Pinned official Mathlib4 v4.35.0 Rat Cast Order/Defs/CharZero sources record these precise statements.

## Exact assignment, complete slot coverage and maps

The local assignment w remains ThreePoleCertificates318.fill pre C₀ C₁ C₂, with pre the original ThreeDetectorUniformFamily318.witness (a:ℚ) labels h t and the SAME certificates from the supplied point pairs at190,241,292. The original preserved_slots producer covers exactly [0,33,37,82,83,118,145]. The candidate gives hslot that complete typed statement in terms of w, using simpa only [w,pre] to instantiate the original producer. No fill, certificate, point, input or index changes, and no subset of the seven slots is used as a substitute.

All existing later rewrite/simp calls are unchanged. They now consume the typed w equations to recover input0, square118, fixed signed root82/83, norm37, quotient/poleInput through0/33/37, and Anchor coefficient145. The original exact hbeq transports P₃ and the same scalar pole; the actual_norm identity transports the original Anchor A. No arbitrary matching point, quotient denominator, chart, scalar restriction or fixed-root sign is substituted. The final actual ScalarCompleteSource318.hasSolution_of_point application retains all original arguments and concludes the full literal stage0 system on the original input a.

## Full domains and actual direct consumers

All rational S, integer a/h, four labels, original nonzero/excluded label1 hypotheses, guard conditions, strict scalar lower bound, ThreeDetectorPrePole constraints, all three positive poles, four actual PointPair inputs and explicit ternary-norm Anchor remain unchanged. No certificate or Anchor existence is inferred from bounds. All original CRT moduli, coprimality/gcd/divisibility conditions, eventual t, arbitrarily large h, full root family and all pole ranges remain in prepared_full_source/current_prepared_full_source.

Inside the same module, scalar_domain is directly consumed in complete_at_index and prepared_full_source; complete_at_index is directly consumed by prepared_full_source, then specialized by current_prepared_full_source. External direct consumer PreparedTwistSource318.current_source_from_twists invokes current_prepared_full_source at its line51 before retaining the original h and requiring actual realizations/local-unit preparation. Its actual application is copied as primary evidence. TwoTwistPointRealization merely imports the module and is not substituted as the consumer.

## Verification boundary

Before e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423; candidate a06b70a2e09101a0474b617e517ba7d8e75493cee84956247af8788cf90faacd. Only the two proof sites change; public statements, definitions, all other proof text, imports and resource options are byte-identical. Ordered1299/1304 closures each change only this canonical source and retain their own exact artifacts/RESULT/intake evidence. No speculative downstream ScalarPolePreparation edit is included. Distinct review and hosted elaboration remain required; no local Lean/Lake, candidate kernel/recursive-audit or full arithmetic acceptance is claimed.
