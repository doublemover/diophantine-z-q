# Exact original word-ideal affine chart classifier

613-source candidate: exact610 plus3 modules.

The generic normalized-frame classifier returns the full annihilator ideal with the specific selected source images as its quotient basis. Conversely an ideal with that actual word basis gives its multiplication action in exactly those coordinates. Normalization uniqueness proves injectivity, and the original quotient kernel identity proves the inverse ideal direction.

The original-source normalized points are then identified in both directions with normalized actions of the literal S⊗[R]A. Both directions preserve the same marked vector and every selected1⊗word-product evaluation, using the exact tensor adjunction inverse and word evaluation formulas.

Composing these explicit equivalences yields an all-ring fixed-word chart classifier from homomorphisms out of the represented normalized coordinate ring to exactly the full original source ideals with the specified word quotient basis. Nilpotents and all original source equations remain present.

This is not yet a global glued classifier: regular overlap maps/cocycles, coefficient ideal-base-change naturality, universal family compatibility and scheme gluing remain separate. No full Picard/Jacobian claim.

No local Lean or profiler executed. Static checks and independent source review are separate from hosted Lean/kernel/axiom acceptance. Frozen598/core remains unchanged.


Two same-equality helpers in CyclicQuotientCanonicalFrame318.equiv_marked now use congrArg evaluation of map_one directly instead of rw[map_one];rfl. This avoids redundant tactic completion risk. No statement, hypothesis, map or later proof changes. No hosted failure was claimed for the former helpers. Exact609 other predecessor sources and all new modules are separately hashed.


## Explicit ideal dependency repair

Exact hosted234 isolated21-core failed at its first source: Ideal was not imported by Bilinear/Isomorphisms. Add public import Mathlib.RingTheory.Ideal.Basic before the actual ideal definition. This is the sole Lean change, all bodies and612 other sources exact. The error-recovery sorry warnings in that failed build were not source admissions and no artifact was accepted. Pinned IdealBasic source is already bound. Fresh review/hosted check required.
