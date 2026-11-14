module
public import ActualTwoDescentFullOverlapMapRestriction318
public section
noncomputable section
namespace ActualTwoDescentOriginalIdealInfinityFrame318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalChartIntersections318
open ActualTwoDescentOriginalRootAffineSheaf318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalOverlapInclusionIsomorphism318 ActualTwoDescentFullOverlapMapRestriction318
variable {K : Type*} [Field K] [CharZero K]

lemma actual_affine_match_on_infinity_isIso (n : K) (i : Fin 3) :
    IsIso ((Scheme.Modules.restrictFunctor (infinityChart n)).map (affineIdealRestriction n i)) := by
  letI := actual_root_overlap_inclusion_isIso n i
  letI := actual_push_restrict_isIso (affineChart n) (infinityChart n) (intoAffine n)
    (rootAffineInclusion n i) (actual_affine_intersection_range n)
  letI := ClutchedModuleFrames318.restriction_isIso (infinityChart n) (affineChart n)
    (intoAffine n) (actual_affine_intersection_range n)
  unfold affineIdealRestriction
  rw [Functor.map_comp]
  infer_instance

lemma actual_infinity_projection_isIso (n : K) (i : Fin 3) :
    IsIso ((Scheme.Modules.restrictFunctor (infinityChart n)).map (infinityProjection n i)) := by
  letI := actual_affine_match_on_infinity_isIso n i
  have h := (IsPullback.of_hasPullback (affineIdealRestriction n i)
    (infinityInverseRestriction n)).map (Scheme.Modules.restrictFunctor (infinityChart n))
  exact h.isIso_snd_of_isIso

/-- A genuine infinity frame of the SAME produced global ideal sheaf,
using its exact infinity projection and the native restriction counit. -/
def originalInfinityFrame (n : K) (i : Fin 3) :
    (originalRootIdealSheaf n i).restrict (infinityChart n) ≅
      SheafOfModules.unit (infinityScheme n).ringCatSheaf := by
  letI := actual_infinity_projection_isIso n i
  exact asIso ((Scheme.Modules.restrictFunctor (infinityChart n)).map (infinityProjection n i)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso (infinityChart n)).app
      (SheafOfModules.unit (infinityScheme n).ringCatSheaf)
end ActualTwoDescentOriginalIdealInfinityFrame318
