module
public import PELOriginalWholeNoetherNormalization318
public import PELOriginalProjectedChartIndependence318
public import PELOriginalAffineChartTranscendence318
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Algebraic.Integral
public section
noncomputable section
namespace PELOriginalTwoDimensionalNormalization318
open PELOriginalCandidateAffineCharts318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- Every whole finite faithful polynomial normalization has exactly
TWO variables. This uses the actual algebraic transcendence-degree bounds,
not a topological dimension inference from equality of point sets. -/
theorem normalization_dimension (n : ℕ)
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (hg : Function.Injective g) (hf : g.Finite) : n = 2 := by
  let R := MvPolynomial (Fin n) ℂ
  let A := CoordinateChart τ hτ j
  letI : Algebra R A := g.toAlgebra
  letI : IsScalarTower ℂ R A :=
    IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  letI : Module.Finite R A := hf
  letI : Algebra.IsAlgebraic R A := ⟨fun a => (IsIntegral.of_finite R a).isAlgebraic⟩
  have ht : Algebra.trdeg ℂ A = 2 := le_antisymm
    (PELOriginalAffineChartTranscendence318.actual_chart_trdeg_le_two τ hτ j)
    (PELOriginalProjectedChartIndependence318.two_le_chart_trdeg τ hτ j)
  have h := trdeg_add_eq ℂ R (A := A)
  rw [trdeg_eq_zero,add_zero,ht] at h
  have hn : (n : Cardinal) = 2 := by simpa [R] using h
  exact_mod_cast hn

/-- A genuine whole normalization with exactly the same dimension as
the original analytic tangent. No derivative claim is attached yet. -/
theorem exists_two_variable_normalization :
    ∃ g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j,
      Function.Injective g ∧ g.Finite := by
  obtain ⟨n,g,hg,hf⟩ :=
    PELOriginalWholeNoetherNormalization318.exists_whole_finite_normalization τ hτ j
  have hn := normalization_dimension τ hτ j n g hg hf
  subst n
  exact ⟨g,hg,hf⟩
end PELOriginalTwoDimensionalNormalization318
