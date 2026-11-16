# Primary Tate tower negation closure repair

Fresh targeted run43864149692 strictly passed the carrier and corrected bounded tower, but the actual AddSubgroup tower's neg_mem proof retained two goals because nsmul_neg is an order-negativity lemma. Replace exactly two simp references with neg_nsmul, the native additive version of inv_pow, to rewrite natural multiplication of a negative element.

Only two lemma-name tokens change. All mathematical definitions, public statements, other proofs and imports are unchanged. All1324 other predecessor sources remain byte-identical, including the newly passed carrier/bounded tower and the residue closure repair in51. This successor revises51, excludes held50, and adds no new mathematical layer. No local Lean or acceptance claim.
