# Coherent source labels and actual detector congruences

This packet proves the local detector root-label congruences at orders4/13 from the literal318 source. It does not assume a logarithm, formal subgroup, analytic approximation, integrality, or rational-ratio oracle.

- OrientedSourceLabels318 chooses actual integer labels for both reciprocal point families, rather than unrelated signs of their difference-root ordinates. The literal scalar orientation/odd anchor is rerun for those exact differences.
- SourceLabelData318.labels_exist supplies one unconditional coherent witness, chosen before any prime. It includes the four actual difference labels, their oddness, the scalar signed index/huge bound, and the common allowed two-torsion offset of H and V.
- GlobalLogRatios318 kills that two-torsion by doubling before applying the actual local logarithm. The global generator need not be locally formal.
- SourcePrimaryRatios318 and SourceAlternateRatios318 identify actual local logarithm ratios with u_i/n and v_i/(n−1), at their correct opposite embeddings. Zero numerator points are included.
- RatioIntegrality318 uses neighboring denominators to bootstrap both actual ratio families to integrality from the literal cross-comparison rows.
- FormalLogDepth318 and SourcePrimaryPrecision318 upgrade the primary whole-series error to absolute precision16. The alternate whole-series Padé/linear errors become16/8.
- SourceContactCongruences318.selected_label_congruences concludes that each literal primary quotient L_i is integral and is congruent to the actual difference label u_i−v_i at precision4 for i=0 and13 for i=1,2,3.
- SourceContactDivisibility318 proves the actual integer Lucas p^13 divisibility and reduced low-target numerator p^4 divisibility for all three literal chains.
- SourceContactContracts318 supplies the full bad-prime ContactDivisibility properties and composes them to the three high/low height bounds. Only the explicitly upstream geometric FiveContact49Height and target nonvanishing remain in those six height wrappers; actual source contact-polynomial nonvanishing is proved.
- SourceSelectedCongruences318 composes each of the three literal rational contact chains with that result. It derives the selected split embedding and all source leaf/domain tests. Only the raw source, its unconditional coherent label witness, a good p≥19, and the consumed positive odd rational contact value are inputs.

The p≥19 hypothesis must come from the full bad-prime exclusions. The contact modulus alone omits13 and does not suffice.

Run `bash run.sh` with the pinned Lean4.35.0/Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679 workspace dependencies. Kernel checking is enabled. The expanded twelve-module recursive audit checks every originating declaration, with only propext, Classical.choice and Quot.sound. receipt.json hashes the full project dependency sources and the fresh verification log. This is an additive packet after checkpoint bcafeb0b20d8321d204f7117b2c72e3ee88679da, not a claim that the entire sourceArithmetic/global height/completeness proof is assembled.
