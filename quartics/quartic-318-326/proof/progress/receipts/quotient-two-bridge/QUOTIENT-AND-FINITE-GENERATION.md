# Actual quotient by 2 and finite generation

This packet proves finite generation of the actual E(Q(sqrt(2))) without a Mordell-Weil or canonical-height premise.

1. `ActualChord318.chord_identities` proves the secant product and coefficient identities for the exact curve. If the two nonzero abscissas have square product, the third abscissa is a square. Its zero case would force a square to equal -D, excluded by the actual real embedding. The equal-abscissa tangent and inverse branches are handled separately in `square_product_sum_double` and `square_product_difference_double`. The actual double is supplied by the unconditional dual-halving theorem.
2. `ActualDoubleQuotient318.pointCode` uses ten labels: the identity, the unique affine point with x=0, and the eight proved first-descent classes. Equal labels imply the actual point difference is a double. Applying this to chosen quotient representatives gives `quotientCode_injective`, an injection from E(K)/2E(K) to Fin10. Hence the quotient has cardinality at most ten and the image of doubling has finite index.
3. `ActualMordellWeil318` constructs the NumberField and ellipticity instances from the actual quadratic field and nonzero discriminant. Mathlib's proved number-field height, Northcott, approximate parallelogram law, and descent theorem then prove `finitely_generated`. Actual torsion finiteness is also proved.

The bound ten deliberately permits unused or duplicate labels; exact index eight is not claimed here. No assertion that the full torsion subgroup is killed by two, free rank one, odd free index, or full global generation is made by this packet. Those are the next group-theoretic steps.

Run `bash run.sh`. The fresh recursive audit covers all declarations in these three modules, permits only propext, Classical.choice and Quot.sound, and uses explicit kernel checking. The separately audited dual-square and first-descent packets are dependencies. Sources, logs and hashes are recorded in receipt.json and SHA256SUMS.
