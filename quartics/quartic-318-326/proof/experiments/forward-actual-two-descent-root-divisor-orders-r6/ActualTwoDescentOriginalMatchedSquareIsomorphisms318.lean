module
public import ActualTwoDescentOriginalRootOverlapRefinement318
public section
noncomputable section
namespace ActualTwoDescentOriginalMatchedSquareIsomorphisms318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalRootNativeSquareCharts318 ActualTwoDescentOriginalOverlapSquareSections318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalOverlapOldFrameComparison318
open ActualTwoDescentNativeTensorMorphismProducts318 ActualTwoDescentOriginalOverlapNativeProduct318
open ActualTwoDescentOriginalMatchedTensorSquare318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The canonical overlap product is literally the native tensor
congruence of the RESTRICTION of the old infinity frame. -/
lemma actual_infinity_product_frame (n : K) (i : Fin 3) :
    infinityProduct n i=(TensorSheafFunctor318.congr (infinityOverlapFrame n i)
      (infinityOverlapFrame n i)).hom ≫ TensorSheafFunctor318.unitIso.hom := by
  unfold infinityProduct product
  rw [←actual_old_infinity_overlap]
  rfl

lemma actual_infinity_square_isIso (n : K) (i : Fin 3) : IsIso (infinitySquare n i) := by
  have hc : IsUnit (infinityCoefficient n i) :=
    (infinitySquareCoefficient_unit n i).map (intoInfinity n).appTop.hom
  letI := ClutchedModule318.multiply_isIso (infinityCoefficient n i) hc
  unfold infinitySquare
  rw [actual_infinity_product_frame]
  infer_instance

lemma actual_affine_square_isIso (n : K) (i : Fin 3) : IsIso (affineSquare n i) := by
  rw [actual_square_maps_match]
  exact actual_infinity_square_isIso n i

/-- Matching on the actual common chart is now equality of genuine
native isomorphisms,not just equality of potentially degenerate maps. -/
def matchedSquareIso (n : K) (i : Fin 3) :
    (IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (originalRootIdealSheaf n i)).restrict
      (overlapEmbedding n) ≅ SheafOfModules.unit (overlapScheme n).ringCatSheaf := by
  letI := actual_infinity_square_isIso n i
  exact TensorOpenRestriction318.iso (overlapEmbedding n) (originalRootIdealSheaf n i)
    (originalRootIdealSheaf n i) ≪≫ asIso (infinitySquare n i)

lemma actual_matched_square_affine (n : K) (i : Fin 3) :
    (matchedSquareIso n i).hom=
    (TensorOpenRestriction318.iso (overlapEmbedding n) (originalRootIdealSheaf n i)
      (originalRootIdealSheaf n i)).hom ≫ affineSquare n i := by
  change _ ≫ infinitySquare n i=_
  rw [actual_square_maps_match]
end ActualTwoDescentOriginalMatchedSquareIsomorphisms318
