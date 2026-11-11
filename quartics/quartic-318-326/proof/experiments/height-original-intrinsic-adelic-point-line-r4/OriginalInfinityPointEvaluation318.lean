module
public import IntegralOverlapCotangentParameter318
public section
noncomputable section
namespace OriginalInfinityPointEvaluation318
open NumberField Polynomial OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open IntegralOverlapCotangentParameter318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1)
  (ht : ¬IsLocalization.IsInteger (V c t v) (t:K c t))
@[expose] def common := IntegralValuativeOverlapPoint318.commonPoint (V c t v) (K c t)
  (localTwists c t v hv) (t:K c t) (roots c t) (local_root_equations c t v hv) ht
@[expose] def finiteEval := finiteEvaluation (V c t v) (localTwists c t v hv) (K c t) (common c t v hv ht)
@[expose] def infinityEval := infinityEvaluation (V c t v) (localTwists c t v hv) (K c t) (common c t v hv ht)
@[expose] def parameterDerivative := derivative (V c t v) (localTwists c t v hv) (K c t) (common c t v hv ht)

theorem finite_polynomial (p : Polynomial (V c t v)) :
    finiteEval c t v hv ht
      (algebraMap (Polynomial (V c t v)) (IntegralBranchCoordinates318.B (V c t v) (localTwists c t v hv) 0) p)=
        Polynomial.aeval (t:K c t) p := by
  change common c t v hv ht
    (IntegralOverlapOpenImmersions318.sourceMap (V c t v) (localTwists c t v hv)
      (algebraMap (Polynomial (V c t v)) _ p))=_
  rw [common,IntegralValuativeOverlapPoint318.commonPoint_source,
    IntegralValuativeGenericPoint318.sourceMap_polynomial]

theorem quartic_value : finiteEval c t v hv ht
    (IntegralBranchBicanonical318.sourceP (V c t v) (localTwists c t v hv) 0)=
      OriginalBranchCotangentFiber318.quarticValue c t := by
  rw [IntegralBranchBicanonical318.sourceP,finite_polynomial]
  simp only [IntegralBranchBicanonical318.quartic,map_prod,map_sub,Polynomial.aeval_X,
    Polynomial.aeval_C,OriginalBranchCotangentFiber318.quarticValue,ContactKummerOrder318.denominator]
  push_cast
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  fin_cases j <;> norm_num [IntegralSourceBranches318.contacts,LinearContactSquareclass318.contacts]

theorem infinity_pair_ratio : infinityEval c t v hv ht
    (IntegralGlobalBicanonicalPair318.infinityCoefficient (V c t v) (localTwists c t v hv) 1)=
      (t:K c t)*infinityEval c t v hv ht
        (IntegralGlobalBicanonicalPair318.infinityCoefficient (V c t v) (localTwists c t v hv) 0) := by
  have h0 := coefficient_transition (V c t v) (localTwists c t v hv) (K c t) (common c t v hv ht) 0
  have h1 := coefficient_transition (V c t v) (localTwists c t v hv) (K c t) (common c t v hv ht) 1
  change infinityEval c t v hv ht _=finiteEval c t v hv ht _*_ at h0 h1
  rw [h0,h1,IntegralOriginalSectionRatios318.branch_coefficients,map_mul]
  have hT : finiteEval c t v hv ht
      (IntegralBranchCoordinates318.sourceT (V c t v) (localTwists c t v hv) 0)=(t:K c t) :=
    (finite_polynomial c t v hv ht X).trans (Polynomial.aeval_X _)
  rw [hT]
  ring

/-- The entire fixed infinity field map is induced by a genuine integral
point of the original infinity order, including all original signed roots. -/
theorem integral_center :
    ∃ φ : IntegralInfinityChart318.Order (V c t v) (localTwists c t v hv) →+* V c t v,
      infinityEval c t v hv ht=(algebraMap (V c t v) (K c t)).comp φ := by
  obtain ⟨u,z,hu,hz,hun,hz2,hd⟩ := IntegralValuativeRootCoordinates318.infinity_coordinates
    (V c t v) (K c t) (localTwists c t v hv) (t:K c t) (roots c t)
    (local_root_equations c t v hv) ht
  exact ⟨IntegralValuativeChartPoints318.infinityMap _ _ u z hz2 hd,
    IntegralValuativeInfinityExtension318.infinity_generic_equality _ _ _ _ _ _ ht u z hz2 hd hu hz⟩
end OriginalInfinityPointEvaluation318
