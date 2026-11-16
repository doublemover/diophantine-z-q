module
public import PELOriginalAllPowerGlobalSections318
public section
noncomputable section
namespace PELOriginalMixedRegularPowerDescent318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAllPowerFrameCoordinates318 PELOriginalSectionMultiplication318
open PELOriginalTranslationFrameValues318 PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalPowerSectionDescent318 PELOriginalPolarizationAutomorphy318
open Filter Topology
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ)

/-- The inputs are genuine regular coefficients with a WHOLE algebraic
cocycle. Analytic continuation and original automorphy are conclusions. -/
structure Data where
  coefficient : ∀ a : NonemptyIndex τ hτ,Γ(candidate τ hτ,opens τ hτ a)
  transition : ∀ a b,(candidate τ hτ).presheaf.map (homOfLE inf_le_left).op (coefficient a)=
    ((LineFrameCocycle318.cocycle (Power τ hτ n) (opens τ hτ)
      (frame τ hτ n)).transition a b).val *
    (candidate τ hτ).presheaf.map (homOfLE inf_le_right).op (coefficient b)

variable (D : Data τ hτ n)
@[expose] def localValue (a : NonemptyIndex τ hτ) (z : ComplexVectors) : ℂ :=
  value τ hτ (opens τ hτ a) (D.coefficient a) z*(chartGauge τ hτ a z)^n

lemma compatible (a b : NonemptyIndex τ hτ) (z : ComplexVectors)
    (ha : z∈chartDomain τ hτ a) (hb : z∈chartDomain τ hτ b) :
    localValue τ hτ n D a z=localValue τ hτ n D b z := by
  have hz : z∈domain τ hτ (opens τ hτ a ⊓ opens τ hτ b) := ⟨ha,hb⟩
  have he := congrArg (fun c => value τ hτ (opens τ hτ a ⊓ opens τ hτ b) c z) (D.transition a b)
  rw [value_mul τ hτ _ _ _ z hz,value_restrict τ hτ _ _ inf_le_left _ z hz,
    value_restrict τ hτ _ _ inf_le_right _ z hz,
    PELOriginalAllPowerFrameCoordinates318.transition_value τ hτ n a b z ha hb] at he
  have hga := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ a.val z (theta_nonzero τ hτ a z ha)
  dsimp only [localValue]
  rw [he,div_pow]
  field_simp [pow_ne_zero n hga]

@[expose] def index (z : ComplexVectors) : NonemptyIndex τ hτ := Classical.choose (chart_cover τ hτ z)
lemma index_mem (z : ComplexVectors) : z∈chartDomain τ hτ (index τ hτ z) :=
  Classical.choose_spec (chart_cover τ hτ z)
@[expose] def entireValue (z : ComplexVectors) : ℂ := localValue τ hτ n D (index τ hτ z) z
lemma chart_formula (a : NonemptyIndex τ hτ) (z : ComplexVectors) (hz : z∈chartDomain τ hτ a) :
    entireValue τ hτ n D z=localValue τ hτ n D a z :=
  compatible τ hτ n D _ a z (index_mem τ hτ z) hz

/-- Arbitrary-open regular-function holomorphy makes this actual glued
cover function entire; no algebraic-to-analytic comparison axiom is used. -/
lemma entire : Differentiable ℂ (entireValue τ hτ n D) := by
  intro z
  let a := index τ hτ z
  have ha : z∈chartDomain τ hτ a := index_mem τ hτ z
  have he : entireValue τ hτ n D =ᶠ[𝓝 z] localValue τ hτ n D a := by
    filter_upwards [(isOpen_domain τ hτ (opens τ hτ a)).mem_nhds ha] with w hw
    exact chart_formula τ hτ n D a w hw
  exact ((differentiableAt_value τ hτ _ _ z ha).mul
    ((PELOriginalMixedTranslationGauge318.gauge_holomorphic τ hτ a.val z
      (theta_nonzero τ hτ a z ha)).pow n)).congr_of_eventuallyEq he

lemma automorphy (l : L τ hτ) (z : ComplexVectors) :
    entireValue τ hτ n D (z+l.val)=factor τ hτ l z^n*entireValue τ hτ n D z := by
  let a := index τ hτ z
  have ha : z∈chartDomain τ hτ a := index_mem τ hτ z
  have hal : z+l.val∈chartDomain τ hτ a :=
    (domain_period τ hτ (opens τ hτ a) l z).mpr ha
  rw [chart_formula τ hτ n D a _ hal,chart_formula τ hτ n D a z ha]
  dsimp only [localValue,chartGauge]
  rw [value_period,PELOriginalMixedTranslationGauge318.gauge_shift τ hτ a.val l z
    (theta_nonzero τ hτ a z ha),mul_pow]
  ring
@[expose] def automorphic : OriginalAutomorphic τ hτ n where
  value := entireValue τ hτ n D
  entire := entire τ hτ n D
  lattice_rule := automorphy τ hτ n D
@[expose] def recovered : homogeneous τ hτ n :=
  ⟨(descend τ hτ n (automorphic τ hτ n D)).value,
    (descend τ hτ n (automorphic τ hτ n D)).holomorphic⟩

/-- Every recovered coefficient equals the supplied WHOLE regular
section, not just its generic or closed-point specialization. -/
lemma coefficient_recovered (a : NonemptyIndex τ hτ) :
    PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n a (recovered τ hτ n D)=D.coefficient a := by
  apply PELOriginalOpenFunctionSeparation318.ext τ hτ (opens τ hτ a)
  intro z hz
  rw [PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ n a _ z hz]
  change PELOriginalPowerSectionLift318.lift τ hτ n (descend τ hτ n (automorphic τ hτ n D)) z / _=_
  rw [lift_descend]
  change entireValue τ hτ n D z/(chartGauge τ hτ a z)^n=_
  rw [chart_formula τ hτ n D a z hz,localValue,mul_div_cancel_right₀ _
    (pow_ne_zero n (PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ a.val z
      (theta_nonzero τ hτ a z hz)))]
end PELOriginalMixedRegularPowerDescent318
