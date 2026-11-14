module
public import ScalarPackedLocalUnit318
public section
noncomputable section
namespace ScalarSmallPrimePreparation318
open ScalarPolePreparation318 ScalarForwardWitness318
set_option maxHeartbeats 0

/-- Exact small-prime normal forms of the actual integer scalar multiplier.
These are the correct current-source values; the2-adic order is4. -/
lemma integerA_shapes (a : ℤ) :
    (∃ k : ℤ, 114444*integerR a=16*(1+8*k)) ∧
    (∃ k : ℤ, 114444*integerR a=9*(1+3*k)) ∧
    (∃ k : ℤ, 114444*integerR a=289*(8+17*k)) := by
  let x := a+a^2
  have he : 2∣x+x^2 := by
    rw [Int.dvd_iff_emod_eq_zero]
    rcases Int.emod_two_eq_zero_or_one x with h|h <;>
      simp [Int.add_emod,Int.pow_emod,h]
  obtain ⟨j,hj⟩ := he
  refine ⟨?_,?_,?_⟩
  · refine ⟨91004161208951682994*x^1+716088952741312363108*x^2+2362325449973424226236*x^3+2814330797291386086912*x^4+3913336234084850038+j,?_⟩
    dsimp [integerR]
    change 114444*(101783690143177584*x+800910366213064752*x^2+2642145132961084032*x^3+3147690941013049344*x^4+4376874610839020)=_
    linear_combination 64*hj
  · refine ⟨431427134620215386048*x^1+3394792072255110462144*x^2+11199172503577714850304*x^3+13342012668640645152768*x^4+18552112517142992773,?_⟩
    dsimp [integerR,x]
    ring
  · refine ⟨2370961252746960192*x^1+18656500295316096576*x^2+61546439567799369216*x^3+73322683096539267072*x^4+101955432111308936,?_⟩
    dsimp [integerR,x]
    ring

lemma value_scaled_unit (p e : ℕ) [Fact p.Prime] (u : ℤ) (hu : ¬(p:ℤ)∣u) :
    padicValRat p ((p:ℚ)^e*(u:ℚ))=(e:ℤ) := by
  have hp : (p:ℚ)≠0 := by exact_mod_cast (Fact.out:p.Prime).ne_zero
  have hu0 : u≠0 := fun hz => hu (hz ▸ dvd_zero _)
  rw [padicValRat.mul (pow_ne_zero _ hp) (by exact_mod_cast hu0),
    padicValRat.pow,padicValRat.self (Fact.out:p.Prime).one_lt,
    padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hu]
  norm_num

lemma actual_multiplier_values (a : ℤ) :
    padicValRat 2 (114444*inputR (a:ℚ))=4 ∧
    padicValRat 3 (114444*inputR (a:ℚ))=2 ∧
    padicValRat 17 (114444*inputR (a:ℚ))=2 := by
  obtain ⟨⟨k₂,h₂⟩,⟨k₃,h₃⟩,⟨k₁₇,h₁₇⟩⟩ := integerA_shapes a
  have hcast : 114444*inputR (a:ℚ)=((114444*integerR a:ℤ):ℚ) := by
    rw [Int.cast_mul,integerR_cast]
    norm_num
  rw [hcast]
  refine ⟨?_,?_,?_⟩
  · letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    rw [h₂,Int.cast_mul]
    convert value_scaled_unit 2 4 (1+8*k₂) (by omega) using 1 <;> norm_num
  · letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [h₃,Int.cast_mul]
    convert value_scaled_unit 3 2 (1+3*k₃) (by omega) using 1 <;> norm_num
  · letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    rw [h₁₇,Int.cast_mul]
    convert value_scaled_unit 17 2 (8+17*k₁₇) (by omega) using 1 <;> norm_num

/-- Once genuine local preparation makes W a unit, all three numerical
preparation-zero valuation thresholds follow at the literal scalar b. -/
theorem actual_pole_thresholds (w : CircuitReplay.Assignment) (n a : ℤ)
    (hin : w 0=(a:ℚ)) (hW : W w n≠0)
    (h₂ : padicValRat 2 (W w n)=0) (h₃ : padicValRat 3 (W w n)=0)
    (h₁₇ : padicValRat 17 (W w n)=0) :
    padicValRat 2 (poleInput w n)=4 ∧ padicValRat 3 (poleInput w n)=2 ∧
      padicValRat 17 (poleInput w n)=2 := by
  obtain ⟨v₂,v₃,v₁₇⟩ := actual_multiplier_values a
  rw [←hin] at v₂ v₃ v₁₇
  have hr : 10< inputR (w 0) := by rw [hin]; exact integer_inputR_large a
  have hA : 114444*inputR (w 0)≠0 := by linarith
  have hD : 1+114444*inputR (w 0)≠0 := by linarith
  refine ⟨?_,?_,?_⟩
  · letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact (support_value 2 _ _ hA hW hD (by omega) h₂).trans v₂
  · letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact (support_value 3 _ _ hA hW hD (by omega) h₃).trans v₃
  · letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
    exact (support_value 17 _ _ hA hW hD (by omega) h₁₇).trans v₁₇

/-- Exact scalar preparation from the original local-leaf inequalities. -/
theorem actual_preparation (w : CircuitReplay.Assignment) (n a : ℤ) (hin : w 0=(a:ℚ))
    (hf : w 33≠0) (hH : w 37≠0) (hn : n≠0) (hn1 : n≠1) (hW : W w n≠0)
    (hprep : ∀ p : ℕ, p.Prime → 0<padicValRat p (114444*inputR (w 0)) →
      padicValRat p (inputR (w 0))<padicValRat p (w 37) ∧
      padicValRat p (inputR (w 0))<padicValRat p (2*w 33) ∧
      2*padicValRat p (w 37)+29*padicValRat p (inputR (w 0))<
        2*padicValRat p (ActualScalarRoot318.inverseNorm n)) :
    IsSquare (poleInput w n).den ∧
      padicValRat 2 (poleInput w n)=4 ∧ padicValRat 3 (poleInput w n)=2 ∧
      padicValRat 17 (poleInput w n)=2 := by
  have hr : inputR (w 0)≠0 := by
    have he := integer_inputR_large a
    rw [←hin] at he
    linarith
  have hunit : ∀ p : ℕ, p.Prime → 0<padicValRat p (114444*inputR (w 0)) →
      padicValRat p (W w n)=0 := by
    intro p hp hs
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨h₁,h₂,h₃⟩ := hprep p hp hs
    exact (ScalarPackedLocalUnit318.actual_unit p w n hr hf hH hn hn1 h₁ h₂ h₃).2
  refine ⟨ScalarPolePreparation318.actual_square_denominator w n a hin hW hunit,?_⟩
  obtain ⟨v₂,v₃,v₁₇⟩ := actual_multiplier_values a
  rw [←hin] at v₂ v₃ v₁₇
  exact actual_pole_thresholds w n a hin hW
    (hunit 2 (by norm_num) (by omega)) (hunit 3 (by norm_num) (by omega))
    (hunit 17 (by norm_num) (by omega))

end ScalarSmallPrimePreparation318
