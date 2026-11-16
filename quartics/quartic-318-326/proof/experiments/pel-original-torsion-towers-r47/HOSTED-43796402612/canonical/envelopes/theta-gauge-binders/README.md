# Actual theta gauge proof-only binders

1. inputs: Same τ,hτ,B. Retain symmetry hB on diagonal_add and retain hB,hperiod on exact_multiplier and original_factor; these existing proof-only variables were omitted from public telescopes.

2. objects: Same original complex vectors, bilinear form, entire quadratic gauge, theta series, full original period Pair and normalized Hermitian factor.

3. domain: Every original z,w and full lattice Pair remain. No domain restriction or finite-index period replacement.

4. maps: Every definition and proof body is byte-identical. No multiplier, normalization, gauge, phase or scalar map changed.

5. scalars: Exact existing complex bilinear symmetry and period-difference equation, including 2I and pi factors. No new instance or inversion.

6. signatures: Three scoped includes intentionally correct public telescopes: include hB on diagonal_add; include hB hperiod on exact_multiplier and original_factor. Before-doc placement preserves exact_multiplier doc ownership. No global include or unrelated signature change.

7. consumer: Existing internal calls already pass hB,hperiod. Actual ThetaGaugeMatrix.original_multiplier supplies derived symmetric τ and period_difference τ hτ; GaugedTheta.original_automorphy and SectionGaugeNormalization.full_period already supply these exact producers.

8. limits: Existing-code repair only, no new mathematical assumption or proof expansion. Residual goals follow the omitted identifiers, but no claim they all compile until hosted replay. No options/import/budget change or local Lean.

9. verification: Own0c61/run43796402612 torsion42 has63 full passes; NormalizedHermitianMatrix3.875s newly passes; ThetaHermitianGauge1.418s fails unknown hB/hperiod plus residuals,671unreached. ed412 torsion42 never compiled after503 and is not evidence here.

