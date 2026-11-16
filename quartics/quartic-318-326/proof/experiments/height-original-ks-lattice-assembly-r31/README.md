# Exact integer-order fraction field bridge

Two modules construct coefficient localization Z[T]→Q[T], transport that localization along the previously constructed rational-fiber equivalence, and descend the existing original Kummer fraction-field theorem to the actual integer order. The field algebra is the composite of the exact two source embeddings; its scalar tower is proved definitionally and injectivity is derived.

Pinned native API: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, RingTheory/PolynomialAlgebra.lean (coefficient algebra and polynomial pushout), RingTheory/Localization/BaseChange.lean (Algebra.isLocalization_iff_isPushout). No new finite-extension, normality, regularity, smoothness or KS premise is introduced or conclusion claimed.

Hosted plan: append these two roots after current KS closure, preserve every predecessor source. First elaborate coefficient localization under the exact named rationalPolynomialAlgebra, then localizedEquiv and source-localization, then exact field algebra/scalar tower and fraction-field descent. Reuse current source dependency gate. No local Lean has been run. Independent source/API review required before thin packet integration.

Next unproved step: identify integral closure of this order with the Z[T] integral closure in the same finite separable field, prove module finiteness and localization compatibility, then glue normalized charts. A normal arithmetic surface is not thereby regular.

## Thin hosted successor

Exact successor of height-original-ks-lattice-assembly-r30 at a080088b. All 195 predecessor sources unchanged, two reviewed modules appended. Only KS registry slot replaced. Exact closure target: OriginalIntegerFractionField318. No normalization, regularity or KS claim. No local Lean.
