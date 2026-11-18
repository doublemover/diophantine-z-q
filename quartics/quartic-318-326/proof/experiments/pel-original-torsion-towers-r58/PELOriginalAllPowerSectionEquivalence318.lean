module
public import PELOriginalMixedRegularPowerDescent318
public section
noncomputable section
namespace PELOriginalAllPowerSectionEquivalence318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAllPowerFrameCoordinates318 PELOriginalAllPowerGlobalSections318
open PELOriginalSectionMultiplication318 PELOriginalTranslationFrameValues318
open PELOriginalOpenRegularFunction318 PELOriginalOpenRegularNaturality318
open PELOriginalPowerSectionLift318 PELOriginalWholeHZeroDimension318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℕ)
@[expose] def data (s : Γ(Power τ hτ n,⊤)) : PELOriginalMixedRegularPowerDescent318.Data τ hτ n where
  coefficient := coefficient τ hτ n s
  transition := coefficient_transition τ hτ n s
@[expose] def recover (s : Γ(Power τ hτ n,⊤)) : homogeneous τ hτ n :=
  PELOriginalMixedRegularPowerDescent318.recovered τ hτ n (data τ hτ n s)
lemma coefficient_recover (s : Γ(Power τ hτ n,⊤)) (a : NonemptyIndex τ hτ) :
    PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n a (recover τ hτ n s)=
      coefficient τ hτ n s a :=
  PELOriginalMixedRegularPowerDescent318.coefficient_recovered τ hτ n (data τ hτ n s) a

lemma original_coefficients_injective : Function.Injective
    (fun s : homogeneous τ hτ n => fun a : NonemptyIndex τ hτ =>
      PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ n a s) := by
  intro s t h
  apply Subtype.ext
  funext q
  obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
  obtain ⟨a,ha⟩ := chart_cover τ hτ z
  have he := congrArg (fun r => value τ hτ (opens τ hτ a) r z) (congrFun h a)
  rw [PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ n a s z ha,
    PELOriginalAllPowerMixedCoefficients318.coefficient_value τ hτ n a t z ha] at he
  have hn := PELOriginalMixedTranslationGauge318.gauge_nonzero τ hτ a.val z (theta_nonzero τ hτ a z ha)
  have hl := (div_left_inj (pow_ne_zero n hn)).mp he
  change (gauge τ hτ n z)⁻¹*s.val (projection (P τ) z)=
    (gauge τ hτ n z)⁻¹*t.val (projection (P τ) z) at hl
  exact mul_left_cancel₀ (inv_ne_zero (gauge_ne_zero τ hτ n z)) hl

theorem recover_algebraize (s : homogeneous τ hτ n) : recover τ hτ n (algebraize τ hτ n s)=s := by
  apply original_coefficients_injective τ hτ n
  funext a
  rw [coefficient_recover,coefficient_algebraize]
theorem algebraize_recover (s : Γ(Power τ hτ n,⊤)) : algebraize τ hτ n (recover τ hτ n s)=s := by
  apply coefficients_injective τ hτ n
  funext a
  rw [coefficient_algebraize,coefficient_recover]

/-- The BOTH-INVERSE comparison for every actual degree-one tensor
power, proved by whole regular coefficients and original automorphy. -/
@[expose] def equivalence : homogeneous τ hτ n ≃ Γ(Power τ hτ n,⊤) where
  toFun := algebraize τ hτ n
  invFun := recover τ hτ n
  left_inv := recover_algebraize τ hτ n
  right_inv := algebraize_recover τ hτ n
lemma coefficient_add (s t : Γ(Power τ hτ n,⊤)) (a : NonemptyIndex τ hτ) :
    coefficient τ hτ n (s+t) a=coefficient τ hτ n s a+coefficient τ hτ n t a := by
  simp only [coefficient,FramedGlobalSectionCoefficients318.coefficient,map_add]
lemma algebraize_add (s t : homogeneous τ hτ n) :
    algebraize τ hτ n (s+t)=algebraize τ hτ n s+algebraize τ hτ n t := by
  apply coefficients_injective τ hτ n
  funext a
  rw [coefficient_algebraize,coefficient_add,coefficient_algebraize,coefficient_algebraize,
    PELOriginalAllPowerMixedCoefficients318.coefficient_add]
@[expose] def additiveEquiv : homogeneous τ hτ n ≃+ Γ(Power τ hτ n,⊤) :=
  { equivalence τ hτ n with map_add' := algebraize_add τ hτ n }
end PELOriginalAllPowerSectionEquivalence318
