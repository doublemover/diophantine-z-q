module
public import ActualTwoDescentOriginalAffineSquareOverlap318
public section
noncomputable section
namespace ActualTwoDescentOriginalThreeSquareCompatibility318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalAffineSquareOverlap318
open ActualTwoDescentOriginalInfinitySquareRestriction318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The three OLD square chart maps now match on the actual complete
intersection. This theorem records only compatibility;global sheaf gluing
and the divisor/theta interpretation are not hidden in its hypotheses. -/
lemma actual_three_old_square_compatibility (n : K) (i : Fin 3) :
    affineSquareOnOverlap n i false=affineSquareOnOverlap n i true ∧
      affineSquareOnOverlap n i false=infinitySquareOnOverlap n i ∧
      affineSquareOnOverlap n i true=infinitySquareOnOverlap n i := by
  simp only [actual_old_affine_square_matches,actual_old_infinity_square_matches,and_self]

lemma actual_old_affine_square_isIso (n : K) (i : Fin 3) (b : Bool) :
    IsIso (affineSquareOnOverlap n i b) := by
  rw [actual_old_affine_square_matches]
  infer_instance
end ActualTwoDescentOriginalThreeSquareCompatibility318
