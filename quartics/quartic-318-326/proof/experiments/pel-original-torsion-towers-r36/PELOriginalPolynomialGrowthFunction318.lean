module
public import PELOriginalFiniteSexticGrowth318
public import PELOriginalSexticInterpolationGrowth318
public section
noncomputable section
namespace PELOriginalPolynomialGrowthFunction318
open QuaternionicRealPeriod318 PolynomialWeightBounds318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalAllLevelHolomorphicMap318
open PELOriginalRatioEvaluationExt318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- Explicit original analytic input to the regularity construction.
The candidate is independently defined, the source is the original
cover, and growth is in actual entire chart-ring coordinate evaluations.
No rationality, algebraicity, normality or regularity conclusion is a field. -/
structure Data where
  onCandidate : Locus τ hτ j → ℂ
  onCover : ComplexVectors → ℂ
  continuous : Continuous onCandidate
  differentiable : ∀ z, value τ hτ 3 j z ≠ 0 → DifferentiableAt ℂ onCover z
  original : ∀ z (hz : value τ hτ 3 j z ≠ 0),
    onCandidate ⟨ratioVector τ hτ 1 j z,
      PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ = onCover z
  growth : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ,
    ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
      ‖onCandidate (toLocus τ hτ j f)‖ ≤
        C*(1+∑ i : Label 3, ‖f (ratioElement τ hτ j i)‖)^N

/-- ANY whole finite normalization supplies a denominator-free bound
for this actual function on ALL its fibers, by integral equations for
the full original coordinate family. -/
theorem fiber_growth (F : Data τ hτ j) {ι X : Type*} [Fintype ι]
    (g : MvPolynomial ι ℂ →ₐ[ℂ] CoordinateChart τ hτ j) (hg : g.Finite)
    (f : X → CoordinateChart τ hτ j →ₐ[ℂ] ℂ) (b : X → ι → ℂ)
    (hsquare : ∀ x r, f x (g r)=MvPolynomial.eval (b x) r) :
    Bounded (fun x => 1+‖b x‖)
      (fun x => ‖F.onCandidate (toLocus τ hτ j (f x))‖) := by
  classical
  let W : X → ℝ := fun x => 1+‖b x‖
  have hW (x : X) : 1 ≤ W x := by dsimp [W]; positivity
  have hi (i : Label 3) : Bounded W (fun x => ‖f x (ratioElement τ hτ j i)‖) :=
    FiniteComplexEvaluationGrowth318.element g hg f b hsquare (ratioElement τ hτ j i)
  have hsum : Bounded W (fun x => 1+∑ i : Label 3, ‖f x (ratioElement τ hτ j i)‖) :=
    add hW (const 1) (sum hW Finset.univ _ (fun i _ => hi i))
  have hnonneg (x : X) : 0 ≤ 1+∑ i : Label 3, ‖f x (ratioElement τ hτ j i)‖ := by positivity
  obtain ⟨C,hC,N,hb⟩ := F.growth
  exact mono (mul (fun x => zero_le_one.trans (hW x)) (const C)
    (pow (fun x => zero_le_one.trans (hW x)) hsum hnonneg N)
    (fun x => pow_nonneg (hnonneg x) N)) (fun x => hb (f x))
end PELOriginalPolynomialGrowthFunction318
