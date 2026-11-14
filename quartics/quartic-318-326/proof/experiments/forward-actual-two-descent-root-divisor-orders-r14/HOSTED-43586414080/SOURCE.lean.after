module
public import TwoTwistPointRealization318
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public section
noncomputable section
namespace ScalarPolePreparation318
open CircuitReplay ScalarForwardWitness318
set_option maxHeartbeats 0

/-- Clearing the fixed coefficient denominators gives an actual integer
polynomial, not merely a positive rational value. -/
@[expose] def integerR (a : ℤ) : ℤ :=
  101783690143177584*(a+a^2)+800910366213064752*(a+a^2)^2+
  2642145132961084032*(a+a^2)^3+3147690941013049344*(a+a^2)^4+4376874610839020

lemma integerR_cast (a : ℤ) : (integerR a:ℚ)=inputR (a:ℚ) := by
  unfold integerR inputR inputFourth inputX
  push_cast
  ring

@[expose] def normalized (A W : ℚ) : ℚ := A*(W/(1+A))^2

lemma normalized_value (p : ℕ) [Fact p.Prime] (A W : ℚ)
    (hA : A≠0) (hW : W≠0) (hD : 1+A≠0) :
    padicValRat p (normalized A W)=padicValRat p A+
      2*(padicValRat p W-padicValRat p (1+A)) := by
  rw [normalized,padicValRat.mul hA (pow_ne_zero _ (div_ne_zero hW hD)),
    padicValRat.pow,padicValRat.div hW hD]
  norm_num

/-- At every positive support prime, the source's unit preparation makes
normalization preserve the exact valuation, including all small-prime thresholds. -/
lemma support_value (p : ℕ) [Fact p.Prime] (A W : ℚ)
    (hA : A≠0) (hW : W≠0) (hD : 1+A≠0)
    (hpos : 0<padicValRat p A) (hunit : padicValRat p W=0) :
    padicValRat p (normalized A W)=padicValRat p A := by
  have hd : padicValRat p (1+A)=0 := by
    simpa using (padicValRat.add_eq_of_lt hD (by norm_num : (1:ℚ)≠0) hA
      (by simpa using hpos))
  rw [normalized_value p A W hA hW hD,hunit,hd]
  ring

/-- Square reduced denominator is a proved consequence of integral A and
unit W at every prime in its support. Integrality alone would not suffice. -/
theorem square_denominator (A W : ℚ) (hA : A≠0) (hW : W≠0) (hD : 1+A≠0)
    (hintegral : ∀ p : ℕ, p.Prime → 0≤padicValRat p A)
    (hunit : ∀ p : ℕ, p.Prime → 0<padicValRat p A → padicValRat p W=0) :
    IsSquare (normalized A W).den := by
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  have hv := normalized_value p A W hA hW hD
  have heven : 0≤padicValRat p (normalized A W) ∨ Even (padicValRat p (normalized A W)) := by
    by_cases hpos : 0<padicValRat p A
    · left
      rw [support_value p A W hA hW hD hpos (hunit p hp hpos)]
      exact le_of_lt hpos
    · right
      have hz : padicValRat p A=0 := by have hi := hintegral p hp; omega
      rw [hv,hz,zero_add]
      exact ⟨padicValRat p W-padicValRat p (1+A),by ring⟩
  have hd : Even (padicValNat p (normalized A W).den) := by
    rcases heven with hnonneg|heven
    · rcases Rat.num_or_den_zero_padicVal (normalized A W) hp with hn|hd
      · have hz : padicValNat p (normalized A W).den=0 := by
          simp only [padicValRat_def,hn,Nat.cast_zero,zero_sub] at hnonneg
          omega
        simp [hz]
      · simp [hd]
    · exact (Rat.num_den_even_padicVal_of_even_padicVal hp heven).2
  simpa only [Nat.factorization_def _ hp] using hd

/-- Apply the denominator argument to the literal scalar pole of the
original integer input. Only the still-needed actual local unit preparation
is left as a premise; r-integrality is supplied here. -/
theorem actual_square_denominator (w : Assignment) (n a : ℤ) (hin : w 0=(a:ℚ))
    (hW : W w n≠0)
    (hunit : ∀ p : ℕ, p.Prime → 0<padicValRat p (114444*inputR (w 0)) →
      padicValRat p (W w n)=0) : IsSquare (poleInput w n).den := by
  have hr : 10 < inputR (w 0) := by rw [hin]; exact integer_inputR_large a
  change IsSquare (normalized (114444*inputR (w 0)) (W w n)).den
  apply square_denominator _ _ (by linarith) hW (by linarith) _ hunit
  intro p hp
  rw [hin,←integerR_cast]
  have he : (114444:ℚ)*(integerR a:ℚ)=((114444*integerR a:ℤ):ℚ) := by push_cast; rfl
  rw [he,padicValRat.of_int]
  exact_mod_cast (Nat.zero_le (padicValInt p (114444*integerR a)))

/-- Local squareclass transport keeps the actual normalization denominator.
The local-square producer for A at2,3,17 remains a separate arithmetic input. -/
lemma normalized_square {F : Type*} [Field F] (σ : ℚ →+* F) (A W : ℚ)
    (hA : IsSquare (σ A)) : IsSquare (σ (normalized A W)) := by
  obtain ⟨x,hx⟩ := hA
  refine ⟨x*σ (W/(1+A)),?_⟩
  rw [normalized,map_mul,map_pow,hx]
  ring

end ScalarPolePreparation318
