module
public import PELOriginalWholeNormalizationRootLift318
public import IntegralElementBaseCutoff318
public import PELOriginalFullLocalizedPoints318
public section
noncomputable section
namespace PELOriginalNormalizationBaseCutoff318
open Polynomial QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalCandidateAffineCharts318 PELOriginalProjectedFiniteOpen318
open PELOriginalOpenPrimitiveSheets318 PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- Every nonzero original chart element has a produced nonzero
polynomial cutoff in ANY finite whole-chart normalization. -/
theorem exists_base_cutoff (n : ℕ)
    (g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j) (hf : g.Finite)
    (a : CoordinateChart τ hτ j) (ha : a ≠ 0) :
    ∃ b : MvPolynomial (Fin n) ℂ, b ≠ 0 ∧
      ∀ (v : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ)
        (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ),
        f.comp g = v → v b ≠ 0 → f a ≠ 0 := by
  let R := MvPolynomial (Fin n) ℂ
  let A := CoordinateChart τ hτ j
  letI : Algebra R A := g.toAlgebra
  letI : Module.Finite R A := hf
  obtain ⟨b,hb,hcut⟩ := IntegralElementBaseCutoff318.exists_cutoff R A a
    (IsIntegral.of_finite R a) ha
  refine ⟨b,hb,?_⟩
  intro v f hs hne
  exact hcut v.toRingHom f.toRingHom (congrArg AlgHom.toRingHom hs) hne

/-- The original common-open realization contains the ENTIRE preimage
of a genuine nonzero polynomial open in a produced WHOLE normalization.
This supplies the exact base cutoff for the remaining topological
density argument; it does not itself assert that density. -/
theorem exists_base_open_original_image (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) :
    ∃ n : ℕ, ∃ g : MvPolynomial (Fin n) ℂ →ₐ[ℂ] CoordinateChart τ hτ j,
      Function.Injective g ∧ g.Finite ∧
      ∃ d : BasePolynomial, d ≠ 0 ∧ polynomialMap τ hτ j x d ≠ 0 ∧
      ∃ b : MvPolynomial (Fin n) ℂ, b ≠ 0 ∧
        ∀ (v : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ)
          (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ),
          f.comp g = v → v b ≠ 0 →
            ∃ z : originalDomain τ hτ j x d,
              ∀ a : CoordinateChart τ hτ j,
                f a = algebraEvaluation τ hτ z.val j z.property.1 a := by
  obtain ⟨n,g,hg,hf⟩ :=
    PELOriginalWholeNoetherNormalization318.exists_whole_finite_normalization τ hτ j
  obtain ⟨d,hd,ha,hfull⟩ :=
    PELOriginalFullLocalizedPoints318.exists_full_chart_open τ hτ j x hx
  obtain ⟨b,hb,hcut⟩ := exists_base_cutoff τ hτ j n g hf (polynomialMap τ hτ j x d) ha
  exact ⟨n,g,hg,hf,d,hd,ha,b,hb,fun v f hs hv => hfull f (hcut v f hs hv)⟩
end PELOriginalNormalizationBaseCutoff318
