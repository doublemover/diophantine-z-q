# Normalize the reciprocity numeral cast

Fresh strict run44005288732 reported a single rewrite error in the native-only split-residue leaf: the reciprocity equality contains jacobiSym of the natural numeral3 cast into integers, while h3 uses the integer numeral3.

Insert only simp only[Nat.cast_ofNat] at that equality before the unchanged rewrite. All theorem statements, assumptions, proof remainder, imports and resource limits stay unchanged. All1353 other source bytes and1354-root order remain unchanged, including priority ternary108 and deferred chart109 repairs.

The same one-root strict check remains required. No selected-prime compatibility or global witness is claimed.
