module
public import OriginalProjectiveFunctionCoordinate318
public import OriginalSchemeDeckFieldAction318
public import ReconstructedFieldNormalization318
public section
noncomputable section
namespace OriginalCanonicalQuotientBase318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y] [IsIntegral (ProjectiveJLine318.scheme ℚ)]
  (p : Y ⟶ ProjectiveJLine318.scheme ℚ) [IsDominant p]
local instance actualBase : Algebra (RatFunc ℚ) Y.functionField :=
  OriginalSchemeDeckFieldAction318.baseAlgebra p OriginalProjectiveFunctionCoordinate318.κ

/-- The actual dominant quotient morphism alone fixes its generic base square
for the canonical t-coordinate. No affine chart or generic base square is
needed as an additional premise. -/
theorem generic_base : OriginalGenericStalkNaturality318.generic Y ≫ p =
    ReconstructedFieldNormalization318.base Y.functionField := by
  rw [OriginalGenericStalkNaturality318.naturality p,
    OriginalProjectiveFunctionCoordinate318.generic_chart, ← Category.assoc, ← Spec.map_comp]
  unfold ReconstructedFieldNormalization318.base
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro q
  rfl
end OriginalCanonicalQuotientBase318
