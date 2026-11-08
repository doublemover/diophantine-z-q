# Actual projective-line affine automorphism

For every commutative ring R, unit a and b in R, the homogeneous substitution X0 ↦ a X0 + b X1, X1 ↦ X1 induces an actual Scheme automorphism of the existing ProjectiveJLine318.scheme R. Its inverse uses a⁻¹ and −a⁻¹b. Both Scheme composition identities are proved, through the actual graded homomorphisms and Proj functor.

ProjectiveAffineCharts318.chart_naturality is the exact finite chart square with Polynomial.aeval (C a * X + C b). map_over_base is the original R-structure square. The dehomogenization computation uses the actual homogeneous localization, with denominator transport made explicit, not a geometric-point argument.

The three unchanged final sources each passed strict kernel checking. Audit.lean imports all declarations, asserts the required endpoint names and recursively checks all 46 declarations against only propext, Classical.choice and Quot.sound. The named successful source logs and exact audit log are retained. Earlier unsuccessful development drafts/logs are excluded. The two official Mathlib sources were compiled from the pinned checkout unchanged; their hashes are retained, not redistributed here. Hosted combined verification and non-author consuming review remain pending.

Immediate consumer: CompletedCharacterFinite318 specializes a to the inverse cubic x scale and b to its centroid. This packet itself does not prove that consumer, normalization/Jacobian/PEL identities or any arithmetic conclusion.
