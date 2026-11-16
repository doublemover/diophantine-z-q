module
public import ActualTwoDescentOriginalChartIntersections318
public import ClutchedModuleFrames318
public section
noncomputable section
namespace ActualTwoDescentOriginalIdealAffineRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalChartIntersections318
open ActualTwoDescentOriginalRootAffineSheaf318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalInverseInfinityTransition318
variable {K : Type*} [Field K] [CharZero K]

/-- On the whole original affine chart the infinity matching morphism
is invertible, using the FULL intersection and the produced u inverse. -/
lemma actual_infinity_match_on_affine_isIso (n : K) :
    IsIso ((Scheme.Modules.restrictFunctor (affineChart n)).map (infinityInverseRestriction n)) := by
  letI := ClutchedModuleFrames318.restriction_isIso (affineChart n) (infinityChart n)
    (intoInfinity n) (actual_infinity_intersection_range n)
  unfold infinityInverseRestriction ClutchedModule318.twistedRestriction
  rw [Functor.map_comp,Functor.map_comp]
  infer_instance

/-- The affine projection of the ACTUAL global pullback sheaf becomes
an isomorphism after actual restriction. This is not assumed descent. -/
lemma actual_affine_projection_isIso (n : K) (i : Fin 3) :
    IsIso ((Scheme.Modules.restrictFunctor (affineChart n)).map (affineProjection n i)) := by
  letI := actual_infinity_match_on_affine_isIso n
  have h := (IsPullback.of_hasPullback (affineIdealRestriction n i)
    (infinityInverseRestriction n)).map (Scheme.Modules.restrictFunctor (affineChart n))
  exact h.isIso_fst_of_isIso

def originalAffineRestrictionIso (n : K) (i : Fin 3) :
    (originalRootIdealSheaf n i).restrict (affineChart n) ≅ rootAffineSheaf n i := by
  letI := actual_affine_projection_isIso n i
  exact asIso ((Scheme.Modules.restrictFunctor (affineChart n)).map (affineProjection n i)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso (affineChart n)).app (rootAffineSheaf n i)
end ActualTwoDescentOriginalIdealAffineRestriction318
