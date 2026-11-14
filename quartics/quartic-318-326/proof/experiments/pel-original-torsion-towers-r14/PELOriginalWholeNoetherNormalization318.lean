module
public import PELOriginalCandidateChartFiniteType318
public import PELOriginalCandidateChartDomains318
public import Mathlib.RingTheory.NoetherNormalization
public section
noncomputable section
namespace PELOriginalWholeNoetherNormalization318
open PELOriginalCandidateAffineCharts318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- A genuine finite faithful polynomial normalization of the WHOLE
original candidate chart. This auxiliary map is for boundary topology;
it does not replace the fixed original projection in earlier results. -/
theorem exists_whole_finite_normalization :
    ∃ n : ℕ, ∃ g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j,
      Function.Injective g ∧ g.Finite := by
  letI : Algebra.FiniteType ℂ (CoordinateChart τ hτ j) :=
    PELOriginalCandidateChartFiniteType318.finite_type τ hτ j
  exact exists_finite_inj_algHom_of_fg ℂ (CoordinateChart τ hτ j)
end PELOriginalWholeNoetherNormalization318
