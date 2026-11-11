module
public import ActualOriginalNonunitFrequency318
public section
noncomputable section
namespace ActualOriginalUnitFourierLayers318
open QuadricCRTAssembly318 ActualOriginalCompleteFourierCount318
open ActualOriginalResidueFourierLift318 ActualOriginalNonunitFrequency318
open ActualOriginalLocalFourierProduct318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- The literal sum over precisely the invertible additive frequencies.
This is the conventional q^-5 singular-series coefficient, not a
complete-frequency average or a layer defined by subtraction. -/
@[expose] def unitAverage (κ : ℤ) (q : ℕ) [NeZero q] : ℂ := by
  classical
  exact (∑ a : {a : ZMod q // IsUnit a}, ∑ x : Coordinates (ZMod q),
    ZMod.stdAddChar (a.val*equation (κ : ZMod q) x)) / (q : ℂ)^5

/-- All nonunit frequencies at a prime power descend to all frequencies
at the previous exponent. Each original residue vector has p^5 lifts. -/
theorem actual_nonunit_sum (κ : ℤ) (p n : ℕ) [NeZero p] (hp : p.Prime) :
    (∑ a : {a : ZMod (p^n*p) // ¬IsUnit a}, ∑ x : Coordinates (ZMod (p^n*p)),
      ZMod.stdAddChar (a.val*equation (κ : ZMod (p^n*p)) x)) =
      (p : ℂ)^5 * completeSum κ (p^n) := by
  classical
  rw [←Equiv.sum_comp (nonunitFrequencyEquiv p n hp)
    (fun a : {a : ZMod (p^n*p) // ¬IsUnit a} =>
      ∑ x : Coordinates (ZMod (p^n*p)), ZMod.stdAddChar (a.val*equation (κ : ZMod (p^n*p)) x))]
  simp only [nonunitFrequencyEquiv_val,scaledFrequency,actual_scaled_phase]
  simp_rw [actual_five_coordinate_sum]
  rw [←Finset.mul_sum]
  rfl

/-- Exact conductor subtraction, including the first prime-power level
where the previous modulus is 1. -/
theorem actual_unit_average_step (κ : ℤ) (p n : ℕ) [NeZero p] (hp : p.Prime) :
    unitAverage κ (p^(n+1)) = completeAverage κ (p^(n+1))-completeAverage κ (p^n) := by
  classical
  rw [pow_succ]
  have hs := Fintype.sum_subtype_add_sum_subtype (fun a : ZMod (p^n*p) => IsUnit a)
    (fun a => ∑ x : Coordinates (ZMod (p^n*p)), ZMod.stdAddChar (a*equation (κ : ZMod (p^n*p)) x))
  rw [actual_nonunit_sum κ p n hp] at hs
  change _ + (p : ℂ)^5*completeSum κ (p^n) = completeSum κ (p^n*p) at hs
  have hsub := eq_sub_of_add_eq hs
  unfold unitAverage completeAverage
  rw [hsub]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  push_cast
  field_simp [hpC]
  <;> ring

lemma actual_unit_average_one (κ : ℤ) : unitAverage κ 1 = completeAverage κ 1 := by
  classical
  have ha (a : ZMod 1) : IsUnit a := by
    have he : a = 1 := Subsingleton.elim _ _
    rw [he]
    exact isUnit_one
  unfold unitAverage completeAverage completeSum
  congr 1
  exact (Finset.sum_subtype Finset.univ (fun a => by simp only [Finset.mem_univ,ha a])
    (fun a : ZMod 1 => ∑ x : Coordinates (ZMod 1), ZMod.stdAddChar (a*equation (κ : ZMod 1) x))).symm

/-- Identification with the previously proved local Fourier layers is
now a theorem about the ACTUAL unit-frequency sums at every exponent. -/
theorem actual_unit_frequency_layers (κ : ℤ) (p : ℕ) [NeZero p] (hp : p.Prime) (n : ℕ) :
    unitAverage κ (p^n) = originalFourierLayers κ p n := by
  cases n with
  | zero => simpa only [pow_zero,originalFourierLayers] using actual_unit_average_one κ
  | succ n => exact actual_unit_average_step κ p n hp

end ActualOriginalUnitFourierLayers318
