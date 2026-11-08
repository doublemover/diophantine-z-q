# Exact coordinates of the existing character morphisms

For all four omitted-contact indices, CubicCoordinateValues318 evaluates the existing cubic-to-published affine algebra equivalence on the actual original t coordinate and character root. Its factors are exactly d^(-1)*q² and d^(-1)*q³, with centroid translation, where d is the complementary twist and q is the already chosen published coordinate scale.

CubicInverseCoordinates318 proves the corresponding inverse formulas using that same equivalence, not a newly chosen affine map. It then transports them through SourceCharacterAlgebra318.toSource to identify the functions of the already constructed finite source-character morphism: x=(d/q²)*(t-centroid) and y=(d/q³)*y_character. These equalities are in the actual entire finite SourceOrder for the fixed original twist tuple units, uniformly for every i : Fin 4.

This is the exact comparison needed before extending the map to the genuine completed elliptic model. It does not itself construct that global extension, identify a relative normalization with the completion, or supply Jacobian/PEL data.

Both exact sources passed bounded strict Lean checks with debug.skipKernelTC=false. Selected logs are preserved. Combined recursive audit and integrated replay remain pending hosted CI; independent source review is pending. This is author-produced evidence, not self-acceptance.
