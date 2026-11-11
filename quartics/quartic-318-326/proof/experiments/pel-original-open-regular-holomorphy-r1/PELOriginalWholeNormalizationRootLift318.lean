module
public import PELOriginalWholeNoetherNormalization318
public import FiniteNormalBaseRootPointLift318
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public section
noncomputable section
namespace PELOriginalWholeNormalizationRootLift318
open Polynomial PELOriginalCandidateAffineCharts318 PELOriginalLevelTheta318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- A single produced whole-chart normalization supports actual monic
minimal polynomials for EVERY original element and lifts EVERY complex
root to a whole original candidate evaluation. All base coordinates and
the chosen original element value are preserved simultaneously. -/
theorem exists_normalization_with_all_root_lifts :
    ∃ n : ℕ, ∃ g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j,
      Function.Injective g ∧ g.Finite ∧
      letI := g.toAlgebra
      ∀ t : CoordinateChart τ hτ j,
        (minpoly (MvPolynomial (Fin n) ℂ) t).Monic ∧
        ∀ (v : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) (z : ℂ),
          ((minpoly (MvPolynomial (Fin n) ℂ) t).map v.toRingHom).eval z = 0 →
            ∃ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ, f.comp g = v ∧ f t = z := by
  obtain ⟨n,g,hg,hf⟩ :=
    PELOriginalWholeNoetherNormalization318.exists_whole_finite_normalization τ hτ j
  refine ⟨n,g,hg,hf,?_⟩
  let R := MvPolynomial (Fin n) ℂ
  let A := CoordinateChart τ hτ j
  letI : Algebra R A := g.toAlgebra
  letI : IsScalarTower ℂ R A :=
    IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : IsTorsionFree R A := isTorsionFree_iff_algebraMap_injective.mpr hg
  letI : Module.Finite R A := hf
  intro t
  refine ⟨FiniteNormalBaseMonogenicSuborder318.monic R A t,?_⟩
  intro v z hz
  obtain ⟨f,hbase,ht⟩ := FiniteNormalBaseRootPointLift318.exists_evaluation R A t v z hz
  refine ⟨f,?_,ht⟩
  ext r
  exact hbase r
end PELOriginalWholeNormalizationRootLift318
