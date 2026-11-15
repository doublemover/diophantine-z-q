module
public import ActualTwoDescentOriginalProjectionFrameAdjoints318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapOldFrameComparison318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalIdealInfinityFrame318 ActualTwoDescentOriginalIdealOverlapValues318
open ActualTwoDescentOriginalProjectionFrameAdjoints318 ActualTwoDescentOpenRestrictionAdjointComposition318
open ActualTwoDescentTildeStructureNormalization318
universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Restrict the OLD actual infinity frame through the exact old
composition and equality-transport maps; no new frame is selected. -/
def infinityOverlapFrame (n : K) (i : Fin 3) : overlapIdeal n i ≅
    SheafOfModules.unit (overlapScheme n).ringCatSheaf :=
  ((Scheme.Modules.restrictFunctorCongr (actual_original_overlap_square n)).app
    (originalRootIdealSheaf n i)).symm ≪≫
  (Scheme.Modules.restrictFunctorComp (intoInfinity n) (infinityChart n)).app
    (originalRootIdealSheaf n i) ≪≫
  (Scheme.Modules.restrictFunctor (intoInfinity n)).mapIso (originalInfinityFrame n i) ≪≫
  Scheme.Modules.restrictUnitIso (intoInfinity n)

lemma actual_old_infinity_overlap (n : K) (i : Fin 3) :
    (infinityOverlapFrame n i).hom=infinityValue n i := by
  apply ((Scheme.Modules.restrictAdjunction (overlapEmbedding n)).homEquiv _ _).injective
  change (Scheme.Modules.restrictAdjunction _).homEquiv _ _
    ((Scheme.Modules.restrictFunctorCongr (actual_original_overlap_square n)).inv.app _ ≫
      (Scheme.Modules.restrictFunctorComp (intoInfinity n) (infinityChart n)).hom.app _ ≫
      (Scheme.Modules.restrictFunctor (intoInfinity n)).map (originalInfinityFrame n i).hom ≫
      (Scheme.Modules.restrictUnitIso (intoInfinity n)).hom)=_
  rw [congr_adjoint,composition,restrictUnit_adjoint,actual_infinity_frame_adjoint]
  simp only [infinityValue,Equiv.apply_symm_apply,infinityPlainRestriction,
    ClutchedModule318.restriction,Category.assoc]

/-- The OLD whole-affine inclusion,restricted through its exact native
comparison,is the canonical affine overlap map used by the matched square. -/
lemma actual_old_affine_overlap (n : K) (i : Fin 3) :
    (Scheme.Modules.restrictFunctorComp (intoAffine n) (affineChart n)).hom.app
      (originalRootIdealSheaf n i) ≫
    (Scheme.Modules.restrictFunctor (intoAffine n)).map (affineInclusionFrame n i) ≫
      (Scheme.Modules.restrictUnitIso (intoAffine n)).hom=affineValue n i := by
  apply ((Scheme.Modules.restrictAdjunction (overlapEmbedding n)).homEquiv _ _).injective
  rw [composition,restrictUnit_adjoint,actual_affine_inclusion_adjoint]
  simp only [affineValue,Equiv.apply_symm_apply,affineIdealRestriction,
    ClutchedModule318.restriction,Category.assoc]

/-- Canonical overlap value is therefore an actual native frame,
not merely a morphism satisfying a scalar formula. -/
lemma actual_infinity_value_isIso (n : K) (i : Fin 3) : IsIso (infinityValue n i) := by
  rw [←actual_old_infinity_overlap]
  infer_instance
lemma actual_affine_value_isIso (n : K) (i : Fin 3) : IsIso (affineValue n i) := by
  letI := actual_infinity_value_isIso n i
  rw [actual_overlap_values]
  infer_instance
end ActualTwoDescentOriginalOverlapOldFrameComparison318
