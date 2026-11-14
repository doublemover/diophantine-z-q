module
public import OriginalInfinityPointEvaluation318
public section
noncomputable section
namespace OriginalInfinityCotangentComparison318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open OriginalInfinityPointEvaluation318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1)
  (ht : ¬IsLocalization.IsInteger (V c t v) (t:K c t))
@[expose] def two_unit : IsUnit (2:V c t v) :=
  IntegralSmoothProperBicanonical318.two_unit _ (ContactFinitePlaceBaseMap318.separation_unit c v hv)
abbrev LocalFiber := IntegralInfinityCotangentFiber318.Fiber (V c t v) (localTwists c t v hv)
  (K c t) (infinityEval c t v hv ht)
@[expose] def localFrame : LocalFiber c t v hv ht ≃ₗ[K c t] K c t :=
  IntegralInfinityCotangentFiber318.frame _ _ (two_unit c t v hv) _ (infinityEval c t v hv ht)
/-- This coefficient comes from the proved identity for actual Dt in the
whole overlap Kähler module, including its signed reciprocal Jacobian. -/
@[expose] def localDt : LocalFiber c t v hv ht :=
  IntegralInfinityCotangentFiber318.parameter _ _ _ (infinityEval c t v hv ht)
    (parameterDerivative c t v hv ht)

theorem localDt_value : localFrame c t v hv ht (localDt c t v hv ht)=parameterDerivative c t v hv ht :=
  IntegralInfinityCotangentFiber318.parameter_value _ _ _ _ _ _

include hn in
theorem localDt_ne : localFrame c t v hv ht (localDt c t v hv ht)≠0 := by
  rw [localDt_value]
  apply IntegralOverlapCotangentParameter318.derivative_ne _ _ _ _ (two_unit c t v hv)
  change finiteEval c t v hv ht
    (IntegralBranchBicanonical318.sourceP (V c t v) (localTwists c t v hv) 0)≠0
  rw [quartic_value]
  exact OriginalBranchCotangentFiber318.quartic_ne c t hn

variable (i : Fin 4)
@[expose] def comparison : LocalFiber c t v hv ht ≃ₗ[K c t]
    OriginalBranchCotangentFiber318.Fiber c t hn i :=
  CotangentParameterComparison318.comparison (localFrame c t v hv ht)
    (OriginalBranchCotangentFiber318.frame c t hn i) (localDt c t v hv ht)
    (OriginalBranchCotangentFiber318.dt c t hn i)
    (localDt_ne c t hn v hv ht) (OriginalBranchCotangentFiber318.dt_ne c t hn i)

theorem preserves_dt : comparison c t hn v hv ht i (localDt c t v hv ht)=
    OriginalBranchCotangentFiber318.dt c t hn i :=
  CotangentParameterComparison318.comparison_parameter _ _ _ _ _ _
@[expose] def derivativeRatio : K c t :=
  OriginalBranchCotangentFiber318.frame c t hn i (OriginalBranchCotangentFiber318.dt c t hn i)/
    localFrame c t v hv ht (localDt c t v hv ht)
theorem derivativeRatio_ne : derivativeRatio c t hn v hv ht i≠0 :=
  div_ne_zero (OriginalBranchCotangentFiber318.dt_ne c t hn i) (localDt_ne c t hn v hv ht)

/-- Exact original first section under the infinity cotangent transition. -/
theorem original_zero : ContactBicanonicalPointHeight318.a0 c t hn i=
    (derivativeRatio c t hn v hv ht i)^2*infinityEval c t v hv ht
      (IntegralGlobalBicanonicalPair318.infinityCoefficient (V c t v) (localTwists c t v hv) 0) := by
  have ha := IntegralOverlapCotangentParameter318.cleared_section (V c t v) (localTwists c t v hv)
    (K c t) (common c t v hv ht) (two_unit c t v hv)
  change finiteEval c t v hv ht _*infinityEval c t v hv ht _=
    (VerticalSection318.J:K c t)^2*(parameterDerivative c t v hv ht)^2 at ha
  rw [quartic_value,←localDt_value] at ha
  exact CotangentParameterComparison318.coefficient_transition
    (localFrame c t v hv ht) (OriginalBranchCotangentFiber318.frame c t hn i)
    (localDt c t v hv ht) (OriginalBranchCotangentFiber318.dt c t hn i)
    (localDt_ne c t hn v hv ht)
    (OriginalBranchCotangentFiber318.quarticValue c t) (VerticalSection318.J:K c t) _ _
    (OriginalBranchCotangentFiber318.quartic_ne c t hn) ha
    (OriginalBranchCotangentFiber318.cleared_original c t hn i)

theorem original_one : ContactBicanonicalPointHeight318.a1 c t hn i=
    (derivativeRatio c t hn v hv ht i)^2*infinityEval c t v hv ht
      (IntegralGlobalBicanonicalPair318.infinityCoefficient (V c t v) (localTwists c t v hv) 1) := by
  rw [ContactBicanonicalPointHeight318.ratio,original_zero,infinity_pair_ratio]
  ring

/-- The induced tensor-square map sends the actual infinity q0 fiber to
the original rational-frame q0 fiber, with no extra section scalar. -/
theorem square_preserves_zero :
    TensorProduct.congr (comparison c t hn v hv ht i) (comparison c t hn v hv ht i)
      (infinityEval c t v hv ht
        (IntegralGlobalBicanonicalPair318.infinityCoefficient (V c t v) (localTwists c t v hv) 0) •
        TensorProduct.tmul (K c t)
          (IntegralInfinityCotangentFiber318.du (V c t v) (localTwists c t v hv) (K c t) (infinityEval c t v hv ht))
          (IntegralInfinityCotangentFiber318.du (V c t v) (localTwists c t v hv) (K c t) (infinityEval c t v hv ht)))=
      ContactBicanonicalPointHeight318.a0 c t hn i •
        TensorProduct.tmul (K c t) (OriginalBranchCotangentFiber318.coordinate c t hn i)
          (OriginalBranchCotangentFiber318.coordinate c t hn i) := by
  rw [original_zero]
  exact CotangentParameterComparison318.square_weighted
    (localFrame c t v hv ht) (OriginalBranchCotangentFiber318.frame c t hn i)
    (localDt c t v hv ht) (OriginalBranchCotangentFiber318.dt c t hn i)
    (localDt_ne c t hn v hv ht) (OriginalBranchCotangentFiber318.dt_ne c t hn i)
    _ _ (IntegralInfinityCotangentFiber318.du_value _ _ (two_unit c t v hv) _ _)
    (OriginalBranchCotangentFiber318.coordinate_value c t hn i) _

/-- The whole infinity chart supplies the actual local cotangent-normalized
bounds, with no assumed integral center or comparison scalar. -/
theorem original_bounds :
    (∀ n : Fin 2, v (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)*
        (v ((derivativeRatio c t hn v hv ht i)^2))⁻¹≤1) ∧
    max (v (ContactBicanonicalPointHeight318.a0 c t hn i))
      (v (ContactBicanonicalPointHeight318.a1 c t hn i))=
        v ((derivativeRatio c t hn v hv ht i)^2) := by
  obtain ⟨φ,hφ⟩ := integral_center c t v hv ht
  apply FinitePlaceChartPairBounds318.infinity_bound c v hv φ _ _ _
    (pow_ne_zero 2 (derivativeRatio_ne c t hn v hv ht i))
  · simpa only [hφ,RingHom.comp_apply] using original_zero c t hn v hv ht i
  · simpa only [hφ,RingHom.comp_apply] using original_one c t hn v hv ht i
end OriginalInfinityCotangentComparison318
