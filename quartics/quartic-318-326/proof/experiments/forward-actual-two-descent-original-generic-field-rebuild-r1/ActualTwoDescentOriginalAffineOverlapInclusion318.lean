module
public import ActualTwoDescentNativeOpenRefinementValues318
public section
noncomputable section
namespace ActualTwoDescentOriginalAffineOverlapInclusion318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentOriginalRootOverlapRefinement318
open ActualTwoDescentOriginalIdealOverlapValues318 ActualTwoDescentOriginalProjectionFrameAdjoints318
open ActualTwoDescentOriginalAffineInclusionFrame318 ActualTwoDescentOriginalRootAffineSheaf318
open ActualTwoDescentOriginalIdealAffineRestriction318 ActualTwoDescentNativeOpenRefinementValues318
open ActualTwoDescentOpenRestrictionAdjointComposition318 ActualTwoDescentTildeStructureNormalization318
open ActualTwoDescentPushedStructureRefinement318
universe u
variable {K : Type u} [Field K] [CharZero K]

lemma actual_principal_value_adjoint (n : K) (i : Fin 3) (b : Bool) :
    (Scheme.Modules.restrictAdjunction (rootLocalizationMorphism n i b ≫ affineChart n)).homEquiv _ _
      (ActualTwoDescentOriginalAffineInclusionFrame318.affineValue n i b)=
    (affineProjection n i ≫ (Scheme.Modules.pushforward (affineChart n)).map (rootAffineInclusion n i)) ≫
      ClutchedModule318.restriction (affineChart n) (rootLocalizationMorphism n i b) := by
  have he : ActualTwoDescentOriginalAffineInclusionFrame318.affineValue n i b=
      (Scheme.Modules.restrictFunctorComp (rootLocalizationMorphism n i b) (affineChart n)).hom.app _ ≫
      (Scheme.Modules.restrictFunctor (rootLocalizationMorphism n i b)).map (affineInclusionFrame n i) ≫
      (Scheme.Modules.restrictUnitIso (rootLocalizationMorphism n i b)).hom := by
    simp only [ActualTwoDescentOriginalAffineInclusionFrame318.affineValue,affineSource,
      affineInclusionFrame,Functor.map_comp,Category.assoc]
  rw [he,composition,restrictUnit_adjoint,actual_affine_inclusion_adjoint]
  simp only [ClutchedModule318.restriction,Category.assoc]

def affineValueOnOverlap (n : K) (i : Fin 3) (b : Bool) : overlapIdeal n i ⟶
    SheafOfModules.unit (overlapScheme n).ringCatSheaf :=
  value (intoRootChart n i b) (rootLocalizationMorphism n i b ≫ affineChart n)
    (overlapEmbedding n) (actual_root_overlap_ambient n i b) (originalRootIdealSheaf n i)
    (ActualTwoDescentOriginalAffineInclusionFrame318.affineValue n i b)

/-- The actual OLD principal affine inclusion has the SAME canonical
overlap value,through the exact old localization refinement and transports. -/
lemma actual_principal_value_matches (n : K) (i : Fin 3) (b : Bool) :
    affineValueOnOverlap n i b=ActualTwoDescentOriginalIdealOverlapValues318.affineValue n i := by
  apply ((Scheme.Modules.restrictAdjunction (overlapEmbedding n)).homEquiv _ _).injective
  rw [affineValueOnOverlap,value_adjoint,actual_principal_value_adjoint]
  simp only [ActualTwoDescentOriginalIdealOverlapValues318.affineValue,Equiv.apply_symm_apply]
  calc
    _ = (affineProjection n i ≫ (Scheme.Modules.pushforward (affineChart n)).map (rootAffineInclusion n i)) ≫
      (ClutchedModule318.restriction (affineChart n) (rootLocalizationMorphism n i b) ≫
        ClutchedModule318.restriction (rootLocalizationMorphism n i b ≫ affineChart n) (intoRootChart n i b) ≫
        (Scheme.Modules.pushforwardCongr (actual_root_overlap_ambient n i b)).hom.app _) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [restriction_refinement (affineChart n) (rootLocalizationMorphism n i b)
        (intoRootChart n i b) (intoAffine n) (actual_root_overlap_factorization n i b)] <;> rfl
end ActualTwoDescentOriginalAffineOverlapInclusion318
