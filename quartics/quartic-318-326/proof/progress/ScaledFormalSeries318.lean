module
public import ScaledCoefficients318
public import IntegralFormalAddition318
public import Mathlib.RingTheory.PowerSeries.Substitution
public section
namespace ScaledFormalSeries318
open PowerSeries

theorem map_subst_univariate {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f g : PowerSeries R) (hg : HasSubst g) :
    PowerSeries.map φ (f.subst g) = (PowerSeries.map φ f).subst (PowerSeries.map φ g) :=
  PowerSeries.map_subst hg f


/-- Rescaling and formal fourth-power substitution compose exactly. -/
theorem rescale_subst_fourth {R : Type*} [CommRing R] (c : R) (f : PowerSeries R) :
    (rescale c f).subst (X^4 : PowerSeries R) = f.subst (C c * X^4 : PowerSeries R) := by
  have hx : HasSubst (X^4 : PowerSeries R) := .of_constantCoeff_zero (by change constantCoeff (X^4 : PowerSeries _) = 0; simp)
  rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X' c) hx,
    subst_smul hx, subst_X hx]
  rw [Algebra.smul_def]
  rfl

variable (p : ℕ) [Fact p.Prime]

@[expose] noncomputable def parameter (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) : ℤ_[p] :=
  D.lift hD * (p : ℤ_[p])^4

@[simp] theorem coe_parameter (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    (parameter p D hD : ℚ_[p]) = D * (p : ℚ_[p])^4 := by
  simp [parameter]

@[expose] noncomputable def integralScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    PowerSeries ℤ_[p] := -X * (ScaledCoefficients318.Hscaled p hp D hD).subst
      (X^4 : PowerSeries ℤ_[p])

@[expose] noncomputable def differentialScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    PowerSeries ℤ_[p] := (ScaledCoefficients318.Bscaled p hp D hD).subst
      (X^4 : PowerSeries ℤ_[p])

@[expose] noncomputable def branchScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    PowerSeries ℤ_[p] := (1-C (parameter p D hD)*X^4) * differentialScaled p hp D hD

theorem map_integralScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    (integralScaled p hp D hD).map PadicInt.Coe.ringHom =
      GenericFormalDifferential318.integral (D * (p : ℚ_[p])^4) := by
  have hx : HasSubst (X^4 : PowerSeries ℤ_[p]) := .of_constantCoeff_zero (by change constantCoeff (X^4 : PowerSeries _) = 0; simp)
  rw [integralScaled, map_mul, map_neg, map_X,
    map_subst_univariate _ _ _ hx, ScaledCoefficients318.map_Hscaled]
  rw [map_pow, map_X, rescale_subst_fourth]
  rfl

theorem map_differentialScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    (differentialScaled p hp D hD).map PadicInt.Coe.ringHom =
      GenericFormalDifferential318.differential (D * (p : ℚ_[p])^4) := by
  have hx : HasSubst (X^4 : PowerSeries ℤ_[p]) := .of_constantCoeff_zero (by change constantCoeff (X^4 : PowerSeries _) = 0; simp)
  rw [differentialScaled, map_subst_univariate _ _ _ hx,
    ScaledCoefficients318.map_Bscaled, map_pow, map_X, rescale_subst_fourth]
  rfl

theorem map_branchScaled (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    (branchScaled p hp D hD).map PadicInt.Coe.ringHom =
      GenericFormalDifferential318.branch (D * (p : ℚ_[p])^4) := by
  simp only [branchScaled, map_mul, map_sub, map_one, map_C, map_pow, map_X,
    PadicInt.Coe.ringHom_apply, coe_parameter, map_differentialScaled,
    GenericFormalDifferential318.branch, GenericFormalDifferential318.argument]

theorem powerSeries_map_injective :
    Function.Injective (PowerSeries.map (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p])) :=
  PowerSeries.map_injective _ (fun _ _ h => PadicInt.ext h)

@[simp] theorem integralScaled_constant (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    constantCoeff (integralScaled p hp D hD) = 0 := by
  simp [integralScaled]

@[simp] theorem branchScaled_constant (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    constantCoeff (branchScaled p hp D hD) = 1 := by
  apply PadicInt.ext
  have h := congrArg (coeff 0) (map_branchScaled p hp D hD)
  simpa only [coeff_map, coeff_zero_eq_constantCoeff_apply,
    PadicInt.Coe.ringHom_apply, GenericFormalDifferential318.branch_constant,
    PadicInt.coe_one] using h

/-- The full two-variable formal addition law for the actual integral scaled series.
Its only hypotheses are primality, p≥19, and integrality of D. -/
theorem formal_addition (hp : 19 ≤ p) (D : ℚ_[p]) (hD : ‖D‖ ≤ 1) :
    (integralScaled p hp D hD).subst
        (IntegralFormalAddition318.f (parameter p D hD) (branchScaled p hp D hD)) =
      (integralScaled p hp D hD).subst (IntegralFormalAddition318.x (R := ℤ_[p])) +
      (integralScaled p hp D hD).subst (IntegralFormalAddition318.a (R := ℤ_[p])) := by
  apply IntegralFormalAddition318.formal_addition PadicInt.Coe.ringHom
    (fun _ _ h => PadicInt.ext h)
  · simpa only [PadicInt.Coe.ringHom_apply, coe_parameter] using
      map_integralScaled p hp D hD
  · simpa only [PadicInt.Coe.ringHom_apply, coe_parameter] using
      map_branchScaled p hp D hD

end ScaledFormalSeries318
#print axioms ScaledFormalSeries318.rescale_subst_fourth
#print axioms ScaledFormalSeries318.map_integralScaled
#print axioms ScaledFormalSeries318.map_branchScaled
#print axioms ScaledFormalSeries318.powerSeries_map_injective
#print axioms ScaledFormalSeries318.branchScaled_constant

#print axioms ScaledFormalSeries318.formal_addition
