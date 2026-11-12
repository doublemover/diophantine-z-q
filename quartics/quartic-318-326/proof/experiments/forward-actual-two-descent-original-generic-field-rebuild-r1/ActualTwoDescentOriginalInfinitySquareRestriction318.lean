module
public import ActualTwoDescentNativeScaledSquareCongruence318
public section
noncomputable section
namespace ActualTwoDescentOriginalInfinitySquareRestriction318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealInfinityFrame318 ActualTwoDescentOriginalRootNativeSquareCharts318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalOverlapOldFrameComparison318
open ActualTwoDescentOriginalOverlapSquareSections318 ActualTwoDescentOriginalMatchedSquareIsomorphisms318
open ActualTwoDescentOriginalMatchedTensorSquare318 ActualTwoDescentOriginalOverlapNativeProduct318
open ActualTwoDescentNativeTensorRestrictionProducts318 ActualTwoDescentNativeScaledSquareRestriction318
open ActualTwoDescentNativeScaledSquareCongruence318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Restriction of the OLD infinity square,with the actual native
embedding equality,composition,frame restriction and structure comparison. -/
def infinitySquareOnOverlap (n : K) (i : Fin 3) :
    (IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (originalRootIdealSheaf n i)).restrict
      (overlapEmbedding n) ⟶ SheafOfModules.unit (overlapScheme n).ringCatSheaf :=
  (Scheme.Modules.restrictFunctorCongr (actual_original_overlap_square n)).inv.app _ ≫
    (Scheme.Modules.restrictFunctorComp (intoInfinity n) (infinityChart n)).hom.app _ ≫
    restrictValue (intoInfinity n) (infinitySquareChart n i).hom

/-- Whole native sheaf morphism identity,not a generic-fiber test or a
replacement frame: the old infinity chart square IS the prior matched square. -/
lemma actual_old_infinity_square_matches (n : K) (i : Fin 3) :
    infinitySquareOnOverlap n i=(matchedSquareIso n i).hom := by
  unfold infinitySquareOnOverlap infinitySquareChart
  rw [squareMap_scaled,squareMap_restrict,squareMap_congr]
  have hf : (Scheme.Modules.restrictFunctorCongr (actual_original_overlap_square n)).inv.app
      (originalRootIdealSheaf n i) ≫
      composedValue (intoInfinity n) (infinityChart n) (originalRootIdealSheaf n i)
        (originalInfinityFrame n i).hom=infinityValue n i := by
    change (infinityOverlapFrame n i).hom=infinityValue n i
    exact actual_old_infinity_overlap n i
  rw [hf] <;> rfl

/-- The very same old infinity restriction also equals the affine
canonical square;this does not yet identify the two old affine square restrictions. -/
lemma actual_old_infinity_square_affine (n : K) (i : Fin 3) :
    infinitySquareOnOverlap n i=
      (TensorOpenRestriction318.iso (overlapEmbedding n) (originalRootIdealSheaf n i)
        (originalRootIdealSheaf n i)).hom ≫ affineSquare n i := by
  rw [actual_old_infinity_square_matches,actual_matched_square_affine]

lemma actual_old_infinity_square_isIso (n : K) (i : Fin 3) :
    IsIso (infinitySquareOnOverlap n i) := by
  rw [actual_old_infinity_square_matches]
  infer_instance
end ActualTwoDescentOriginalInfinitySquareRestriction318
