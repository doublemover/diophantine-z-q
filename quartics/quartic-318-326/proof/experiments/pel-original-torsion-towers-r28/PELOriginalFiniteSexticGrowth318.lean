module
public import FiniteComplexEvaluationGrowth318
public import PELOriginalSexticRatioGrowth318
public import PELOriginalWholeChartNormal318
public section
noncomputable section
namespace PELOriginalFiniteSexticGrowth318
open QuaternionicRealPeriod318 PolynomialWeightBounds318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalSexticChartRatios318
open PELOriginalSexticRatioCover318 PELOriginalSectionMultiplication318
open PELOriginalRatioEvaluationExt318 PELOriginalAllLevelHolomorphicMap318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- The compact original sextic estimate at EVERY whole chart algebra
point. Complete original point realization supplies the source value;
no point is restricted to the old primitive denominator open. -/
theorem point_bound (s : homogeneous τ hτ 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
      ‖candidateRatio τ hτ j s (toLocus τ hτ j f)‖ ≤
        C*∑ i : Label 3, ‖f (ratioElement τ hτ j i)‖^2 := by
  obtain ⟨C,hC,hb⟩ := PELOriginalSexticRatioGrowth318.cover_ratio_bound τ hτ s
  refine ⟨C,hC,?_⟩
  intro f
  obtain ⟨z,hz,hf⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
  have hlocus : toLocus τ hτ j f =
      (⟨ratioVector τ hτ 1 j z,
        PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ : Locus τ hτ j) := by
    apply Subtype.ext
    rw [hf]
    exact PELOriginalFullCandidatePoints318.pointVector_original τ hτ j z hz
  rw [hlocus,candidate_original]
  simpa only [hf,actual_ratio_evaluation] using hb j z hz

/-- ANY actual whole finite normalization gives denominator-free
polynomial growth of EVERY whole sextic section on ALL its complex
fibers. This is stronger than the old fixed-projection pole bound and
uses the integral equations of the whole original chart coordinates. -/
theorem fiber_growth {ι X : Type*} [Fintype ι]
    (g : MvPolynomial ι ℂ →ₐ[ℂ] CoordinateChart τ hτ j) (hg : g.Finite)
    (f : X → CoordinateChart τ hτ j →ₐ[ℂ] ℂ) (b : X → ι → ℂ)
    (hsquare : ∀ x r, f x (g r)=MvPolynomial.eval (b x) r)
    (s : homogeneous τ hτ 6) :
    Bounded (fun x => 1+‖b x‖)
      (fun x => ‖candidateRatio τ hτ j s (toLocus τ hτ j (f x))‖) := by
  classical
  let W : X → ℝ := fun x => 1+‖b x‖
  have hW (x : X) : 1 ≤ W x := by dsimp [W]; positivity
  have hi (i : Label 3) : Bounded W (fun x => ‖f x (ratioElement τ hτ j i)‖^2) :=
    pow (fun x => zero_le_one.trans (hW x))
      (FiniteComplexEvaluationGrowth318.element g hg f b hsquare (ratioElement τ hτ j i))
      (fun x => norm_nonneg _) 2
  obtain ⟨C,hC,hb⟩ := point_bound τ hτ j s
  exact mono (mul (fun x => zero_le_one.trans (hW x)) (const C)
    (sum hW Finset.univ _ (fun i _ => hi i))
    (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))) (fun x => hb (f x))
end PELOriginalFiniteSexticGrowth318
