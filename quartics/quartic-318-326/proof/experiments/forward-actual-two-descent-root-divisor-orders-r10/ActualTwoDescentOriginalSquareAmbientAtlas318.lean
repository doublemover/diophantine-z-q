module
public import ActualTwoDescentOpenChartRefinementCoordinates318
public section
noncomputable section
namespace ActualTwoDescentOriginalSquareAmbientAtlas318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealOpenFrameCover318 ActualTwoDescentOriginalRootNativeSquareCharts318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalRootOverlapRefinement318
open ActualTwoDescentOriginalRootFullOverlap318 ActualTwoDescentOriginalMatchedSquareIsomorphisms318
open ActualTwoDescentOriginalAffineSquareOverlap318 ActualTwoDescentOriginalInfinitySquareRestriction318
open ActualTwoDescentNativeOpenRefinementValues318
universe u
variable {K : Type u} [Field K] [CharZero K]

abbrev squareModule (n : K) (i : Fin 3) :=
  IntrinsicTensorSheaf318.tensor (originalRootIdealSheaf n i) (originalRootIdealSheaf n i)

def chartSquare (n : K) (i : Fin 3) (a : Option Bool) :
    (squareModule n i).restrict (embedding n i a) ≅ SheafOfModules.unit (chart n i a).ringCatSheaf := by
  cases a with
  | none => exact infinitySquareChart n i
  | some b => exact affineSquareChart n i b

def refinement (n : K) (i : Fin 3) : (a : Option Bool) → overlapScheme n ⟶ chart n i a
  | none => intoInfinity n
  | some b => intoRootChart n i b
instance refinement_open (n : K) (i : Fin 3) (a : Option Bool) : IsOpenImmersion (refinement n i a) := by
  cases a <;> infer_instance
lemma refinement_square (n : K) (i : Fin 3) (a : Option Bool) :
    refinement n i a ≫ embedding n i a=overlapEmbedding n := by
  cases a with
  | none => exact actual_original_overlap_square n
  | some b => exact actual_root_overlap_ambient n i b

lemma actual_chart_square_refinement (n : K) (i : Fin 3) (a : Option Bool) :
    value (refinement n i a) (embedding n i a) (overlapEmbedding n) (refinement_square n i a)
      (squareModule n i) (chartSquare n i a).hom=(matchedSquareIso n i).hom := by
  cases a with
  | none =>
    simpa only [value,source,infinitySquareOnOverlap,Category.assoc] using
      actual_old_infinity_square_matches n i
  | some b => exact actual_old_affine_square_matches n i b

/-- Every DISTINCT pair in the actual three-chart atlas has precisely
the complete original common chart as intersection. -/
lemma actual_distinct_intersection (n : K) (i : Fin 3) (a b : Option Bool) (hab : a≠b) :
    (embedding n i a).opensRange ⊓ (embedding n i b).opensRange=(overlapEmbedding n).opensRange := by
  cases a with
  | none =>
    cases b with
    | none => exact (hab rfl).elim
    | some b => exact (inf_comm _ _).trans (actual_affine_infinity_full_overlap n i b)
  | some a =>
    cases b with
    | none => exact actual_affine_infinity_full_overlap n i a
    | some b =>
      cases a <;> cases b
      · exact (hab rfl).elim
      · exact actual_affine_pair_full_overlap n i
      · exact (inf_comm _ _).trans (actual_affine_pair_full_overlap n i)
      · exact (hab rfl).elim
end ActualTwoDescentOriginalSquareAmbientAtlas318
