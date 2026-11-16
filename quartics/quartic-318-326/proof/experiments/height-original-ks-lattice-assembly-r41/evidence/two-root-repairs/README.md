# Two exact fresh KS31 compiler-root repairs

Evidence: hosted run43847457974, height-original-ks-lattice-assembly-r31-se783cd6c00a036a5. Both before-source hashes match the authenticated compiler-error records exactly.

1. IntegerPolynomialLocalization318: the named `rationalPolynomialAlgebra` is semireducible, so native instance matching cannot find the polynomial pushout under that algebra. Prove its equality to native `Polynomial.algebra ℤ ℚ` using `algebra_ext` and the literal coefficient map, prove localization under the native algebra, then transport back to the original named algebra. The statement and exact coefficient map remain unchanged; no localization or pushout premise added.
2. IntegralFourRootOverlap318: remove one extra close parenthesis in the local composition identity at line74. The logged unsolved composition/open-immersion goals occurred before the parser rejected the subsequent proof; the existing `rw [←Spec.map_comp]; rfl` and conclusion now parse as intended. No mathematical proof or declaration statement changed.

Native APIs pinned to mathlib56a005855ea17e0b0958f73ec801ae140b0a1679 are copied under native/. No local Lean, no new options, no axioms/admissions. Source repair candidates pending independent review and exact hosted recheck. These repairs do not establish acceptance of previously blocked global/proper/normalization targets.
