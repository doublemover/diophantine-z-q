module
public import PELOriginalTwoDimensionalNormalization318
public import FiniteCenteredPowerPerturbation318
public import PointDerivationPowerPerturbation318
public import PELOriginalChartTangentDerivation318
public import PELOriginalProjectedChartIndependence318
public section
noncomputable section
namespace PELOriginalFiniteFirstJetNormalization318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalChartEvaluationRegularity318 PELOriginalChartTangentDerivation318
open PELOriginalProjectedChartIndependence318 PELOriginalLevelThreeLocalImage318
open PELOriginalAllLevelHolomorphicMap318 Filter Topology
variable (τ : ℂ) (hτ : 0 < τ.im) (x : ComplexVectors) (j : Label 3)
  (hj : value τ hτ 3 j x ≠ 0)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- The prescribed linear ratio combinations have exactly the identity
first jet on the original analytic tangent, by its actual derivative
left inverse. -/
lemma projected_first_jet (v : ComplexVectors) (k : Fin 2) :
    tangentDerivation τ hτ x j hj v (projectedFunction τ hτ x j k) = v k := by
  let F : ComplexVectors → ComplexVectors := fun y k =>
    evaluate τ hτ j (projectedFunction τ hτ x j k) y
  have he : F =ᶠ[𝓝 x] SplitHolomorphicImage318.projected (ratioVector τ hτ 1 j) x := by
    filter_upwards [(PELOriginalLevelPowerSections318.holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hj] with y hy
    funext i
    rw [evaluate_on_chart τ hτ j _ y hy,projected_evaluation]
    rfl
  have hd : HasFDerivAt F (ContinuousLinearMap.id ℂ ComplexVectors) x :=
    (SplitHolomorphicImage318.projected_hasFDerivAt (ratioVector τ hτ 1 j) x
      (PELOriginalLevelThetaStrictDerivative318.ratio_contDiffAt τ hτ 1 j x hj)
      (PELOriginalLevelThreeTangentSeparation318.chart_derivative_injective τ hτ x j hj)).congr_of_eventuallyEq he
  have hk := (ContinuousLinearMap.proj k : ComplexVectors →L[ℂ] ℂ).hasFDerivAt.comp x hd
  rw [tangentDerivation_apply]
  exact congrArg (fun f : ComplexVectors →L[ℂ] ℂ => f v) hk.fderiv

/-- A WHOLE finite two-coordinate normalization with the specified first
jet at the actual original point. It is constructed by centered high
powers of an actual whole normalization plus the original derivative
left-inverse functions. No generic-open finiteness is substituted. -/
theorem exists_finite_identity_jet :
    ∃ g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j,
      g.Finite ∧
      (∀ v : ComplexVectors, ∀ k : Fin 2,
        tangentDerivation τ hτ x j hj v (g (MvPolynomial.X k)) = v k) ∧
      (∀ k : Fin 2, algebraEvaluation τ hτ x j hj (g (MvPolynomial.X k)) =
        localProjection τ hτ x j (ratioVector τ hτ 1 j x) k) := by
  obtain ⟨g₀,hg₀,hfin₀⟩ :=
    PELOriginalTwoDimensionalNormalization318.exists_two_variable_normalization τ hτ j
  let b : Fin 2 → CoordinateChart τ hτ j := fun k => g₀ (MvPolynomial.X k)
  have hb : (MvPolynomial.aeval b).Finite := by
    have h : MvPolynomial.aeval b = g₀ := by ext k; simp [b]
    rwa [h]
  let l := projectedFunction τ hτ x j
  let v₀ := algebraEvaluation τ hτ x j hj
  obtain ⟨M,hM,hfinite,hcenter⟩ :=
    FiniteCenteredPowerPerturbation318.exists_centered_perturbation b l hb v₀
  let a : Fin 2 → CoordinateChart τ hτ j := fun k =>
    l k+(b k-algebraMap ℂ (CoordinateChart τ hτ j) (v₀ (b k)))^M
  refine ⟨MvPolynomial.aeval a,hfinite,?_,?_⟩
  · intro v k
    rw [MvPolynomial.aeval_X]
    exact (PointDerivationPowerPerturbation318.first_jet v₀
      (tangentDerivation τ hτ x j hj v) (b k) (l k) M hM).trans
        (projected_first_jet τ hτ x j hj v k)
  · intro k
    rw [MvPolynomial.aeval_X]
    exact (hcenter k).trans (projected_evaluation τ hτ x x j hj k)
end PELOriginalFiniteFirstJetNormalization318
