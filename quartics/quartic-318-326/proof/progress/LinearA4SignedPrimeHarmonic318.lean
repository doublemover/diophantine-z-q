module
public import LinearA4PrimeAnalyticBounds318
public import LinearA4GaussianCounts318
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public section
noncomputable section

namespace LinearA4SignedPrimeHarmonic318
open scoped BigOperators
open ZMod LinearA4PrimeAnalyticBounds318

/-- The exact level-four character of the Gaussian rank-two factors. -/
@[expose] def chi4 (p : ℕ) : ℝ := (χ₄ (p:ZMod 4):ℤ)

theorem prime_character (p : ℕ) [Fact p.Prime] (hp2 : p≠2) :
    (LinearA4GaussianCounts318.χ (ZMod p):ℝ) = chi4 p := by
  have hh := legendreSym.at_neg_one hp2
  have hi : quadraticChar (ZMod p) (-1:ZMod p)=χ₄ (p:ZMod 4) := by
    simpa only [legendreSym,Int.cast_neg,Int.cast_one] using hh
  change (quadraticChar (ZMod p) (-1:ZMod p):ℝ) = chi4 p
  exact congrArg (fun z : ℤ => (z:ℝ)) hi

theorem chi_abs (n : ℕ) : |chi4 n|≤1 := by
  rcases isQuadratic_χ₄ (n:ZMod 4) with h|h|h <;> simp [chi4,h]

/-- Analytic donor shape: uniform lower bound on the actual finite
level-four Euler product at exponent one. The exact historical theorem
ActualGlobalCharacterLower318.actual_global_character_lower produces
this from its level-four L-boundary and moving-tail comparison. -/
@[expose] def CharacterEulerLower : Prop :=
  ∃ c : ℝ, 0<c ∧ ∀ y : ℕ,
    c ≤ ∏ p ∈ Nat.primesLE y,(1-chi4 p/(p:ℝ))⁻¹

theorem log_inverse_upper (x : ℝ) (hhalf : x≤1/2) :
    Real.log ((1-x)⁻¹) ≤ x+2*x^2 := by
  have h : 0<1-x := by linarith
  have one : (1-x)⁻¹-1=x/(1-x) := by
    field_simp [h.ne']
    ring
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
  rw [one] at hl
  apply hl.trans
  apply (div_le_iff₀ h).2
  nlinarith [mul_nonneg (sq_nonneg x) (show 0≤1-2*x by linarith)]

theorem pointwise_factor (p : ℕ) (hp : p.Prime) :
    0<1-chi4 p/(p:ℝ) ∧
      Real.log ((1-chi4 p/(p:ℝ))⁻¹) ≤ chi4 p/(p:ℝ)+2/(p:ℝ)^2 := by
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp.two_le
  have hp0 : 0<(p:ℝ) := (by norm_num : (0:ℝ)<2).trans_le hp2
  have hl : |chi4 p/(p:ℝ)|≤1/(p:ℝ) := by
    rw [abs_div,abs_of_pos hp0]
    exact div_le_div_of_nonneg_right (chi_abs p) hp0.le
  have hq : chi4 p/(p:ℝ)≤1/2 := (abs_le.mp
    (hl.trans (one_div_le_one_div_of_le (by norm_num) hp2))).2
  refine ⟨by linarith,?_⟩
  have hs := pow_le_pow_left₀ (abs_nonneg _) hl (n := 2)
  rw [sq_abs] at hs
  have h := log_inverse_upper _ hq
  have he : 2*(1/(p:ℝ))^2=2/(p:ℝ)^2 := by ring
  linarith only [h,hs,he]

/-- The exact signed harmonic lower bound outside any fixed wheel.
Deleting a prime can only increase the size of the error allowance by
its reciprocal; the omitted set is independent of the cutoff. -/
theorem signed_harmonic (hEuler : CharacterEulerLower) (wheel : Finset ℕ) :
    ∃ A : ℝ, ∀ y : ℕ,
      -A ≤ ∑ p ∈ Nat.primesLE y \ wheel,chi4 p/(p:ℝ) := by
  obtain ⟨c,hc,hcLower⟩ := hEuler
  refine ⟨2*squareBudget-Real.log c + ∑ p ∈ wheel,1/(p:ℝ),?_⟩
  intro y
  have hP : 0<∏ p ∈ Nat.primesLE y,(1-chi4 p/(p:ℝ))⁻¹ :=
    Finset.prod_pos (fun p hp => inv_pos.mpr (pointwise_factor p (Nat.mem_primesLE.mp hp).2).1)
  have hl := (Real.log_le_log_iff hc hP).mpr (hcLower y)
  rw [Real.log_prod (fun p hp =>
    inv_ne_zero (pointwise_factor p (Nat.mem_primesLE.mp hp).2).1.ne')] at hl
  have hsum := hl.trans (Finset.sum_le_sum (fun p hp =>
    (pointwise_factor p (Nat.mem_primesLE.mp hp).2).2))
  rw [Finset.sum_add_distrib] at hsum
  have he :
      (∑ p ∈ Nat.primesLE y,2/(p:ℝ)^2) =
        2*(∑ p ∈ Nat.primesLE y,1/(p:ℝ)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he] at hsum
  have hdis := Finset.sum_sdiff (f := fun p : ℕ => chi4 p/(p:ℝ))
    (Finset.inter_subset_left : Nat.primesLE y∩wheel⊆Nat.primesLE y)
  have hr : Nat.primesLE y \ (Nat.primesLE y ∩ wheel) = Nat.primesLE y \ wheel := by
    ext p
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto
  rw [hr] at hdis
  have hbound : (∑ p ∈ Nat.primesLE y∩wheel,chi4 p/(p:ℝ))≤∑ p ∈ wheel,1/(p:ℝ) := by
    calc
      _ ≤ ∑ p ∈ Nat.primesLE y∩wheel,1/(p:ℝ) := by
        apply Finset.sum_le_sum
        intro p _
        exact div_le_div_of_nonneg_right ((abs_le.mp (chi_abs p)).2) (by positivity)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => by positivity)
  linarith only [hsum,hdis,hbound,square_error_budget (Nat.primesLE y)]

end LinearA4SignedPrimeHarmonic318
