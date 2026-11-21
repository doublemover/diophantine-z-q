module
public import ActualRayConductorRows318
public import OriginalInteriorTelescoping318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualSquarefreeWheelConductor16318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayPeriodicRectangle318 ActualRayConductorRows318

@[expose] def oddWheel (y : ℕ) : ℕ :=
  ∏ p∈((Finset.range (y+1)).filter Nat.Prime).erase 2,p

theorem wheel_split {y : ℕ} (hy : 2≤y) : wheel y=2*oddWheel y := by
  have h : 2∈(Finset.range (y+1)).filter Nat.Prime :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hy),Nat.prime_two⟩
  exact (Finset.mul_prod_erase _ (fun p => p) h).symm

theorem oddWheel_coprime (y : ℕ) : (oddWheel y).Coprime 2 := by
  unfold oddWheel
  apply Nat.Coprime.prod_left
  intro p hp
  exact (Nat.coprime_primes (Finset.mem_filter.mp (Finset.mem_erase.mp hp).2).2
    Nat.prime_two).mpr (Finset.mem_erase.mp hp).1

theorem positive_wheel (y : ℕ) : 0<wheel y := by
  unfold wheel
  exact Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.pos

theorem odd_support_dvd_oddWheel {R y : ℕ} (hs : Squarefree R)
    (h : ∀ p : ℕ,p.Prime→p∣R→p≠2 ∧ p≤y) : R∣oddWheel y := by
  rw [←Nat.prod_primeFactors_of_squarefree hs]
  unfold oddWheel
  apply Finset.prod_dvd_prod_of_subset _ _ (fun p => p)
  intro p hp
  have hP := Nat.prime_of_mem_primeFactors hp
  obtain ⟨hne,hpy⟩ := h p hP (Nat.dvd_of_mem_primeFactors hp)
  exact Finset.mem_erase.mpr ⟨hne,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpy),hP⟩⟩

/-- Arithmetic calculation of the full lcm. The ordinary wheel has
one copy of 2, the actual conductor five; all odd factors are already
in W. No class-field hypothesis is proved by this lemma. -/
theorem lcm_32 (V R : ℕ) (hc : V.Coprime 2) (hR : R∣V) :
    (2*V).lcm (32*R)=32*V := by
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · exact ⟨16,by ring⟩
    · obtain ⟨d,hd⟩ := hR
      exact ⟨d,by rw [hd]; ring⟩
  · have h32 : 32∣(2*V).lcm (32*R) :=
      (show 32∣32*R from ⟨R,rfl⟩).trans (Nat.dvd_lcm_right _ _)
    have hV : V∣(2*V).lcm (32*R) :=
      (show V∣2*V from ⟨2,Nat.mul_comm _ _⟩).trans (Nat.dvd_lcm_left _ _)
    have h : (32:ℕ).Coprime V := by simpa only [show 2^5= (32:ℕ) by decide] using hc.symm.pow_left 5
    exact h.mul_dvd_of_dvd_of_dvd h32 hV

theorem wheel_lcm_32 {R y : ℕ} (hy : 2≤y) (hR : R∣oddWheel y) :
    (wheel y).lcm (32*R)=16*wheel y := by
  rw [wheel_split hy,lcm_32 _ _ (oddWheel_coprime y) hR] <;> ring

theorem wheel_period_16 {R y : ℕ} (hy : 2≤y) (hR : R∣oddWheel y) :
    (wheel y).lcm (32*R)/wheel y=16 := by
  rw [wheel_lcm_32 hy hR,Nat.mul_comm 16]
  exact Nat.mul_div_cancel_left _ (positive_wheel y)

theorem period_of_exact_conductor {y F R : ℕ} (hy : 2≤y) (hF : F=32*R)
    (hR : Squarefree R) (hSupport : ∀ p : ℕ,p.Prime→p∣R→p≠2 ∧ p≤y) :
    (wheel y).lcm F/wheel y=16 := by
  rw [hF]
  exact wheel_period_16 hy (odd_support_dvd_oddWheel hR hSupport)

theorem period_16_divides {y F R : ℕ} (hy : 2≤y) (hF : F=32*R)
    (hR : R∣oddWheel y) : F∣wheel y*16 := by
  have h := divides_row_period (wheel y) F
  rw [hF,wheel_period_16 hy hR] at h
  simpa only [hF] using h

/-- Sharper than the coarse 16(n+m) strip budget: the real discarded
widths are n mod 16 and m mod 16, at most 15. -/
theorem rectangle_16_error (f : ℕ→ℕ→ℝ) (hf : Periods 16 f)
    (a z n m : ℕ) (A : ℝ) (hval : ∀ i j,0≤f i j ∧ f i j≤A) :
    |rectangle f a z n m-(n:ℝ)*(m:ℝ)*mean f 16|≤
      15*((n:ℝ)+(m:ℝ))*A := by
  have hA : 0≤A := (hval 0 0).1.trans (hval 0 0).2
  have hn₀ : (n/16)*16≤n := by
    have h := Nat.div_add_mod' n 16
    omega
  have h1 : ((((n/16)*16:ℕ):ℝ))≤(n:ℝ) := by exact_mod_cast hn₀
  have hm : (m%16:ℕ)≤15 := by omega
  have hn : (n%16:ℕ)≤15 := by omega
  have h2 : ((m%16:ℕ):ℝ)≤15 := by exact_mod_cast hm
  have h3 : ((n%16:ℕ):ℝ)≤15 := by exact_mod_cast hn
  have hw : ((((n/16)*16:ℕ):ℝ))*((m%16:ℕ):ℝ)+((n%16:ℕ):ℝ)*(m:ℝ)≤
      15*((n:ℝ)+(m:ℝ)) := by
    calc
      _≤(n:ℝ)*15+15*(m:ℝ) := add_le_add
        (mul_le_mul h1 h2 (by positivity) (by positivity))
        (mul_le_mul_of_nonneg_right h3 (by positivity))
      _=_ := by ring
  exact (rectangle_mean_error_exact f 16 (by decide) hf a z n m A hval).trans
    (mul_le_mul_of_nonneg_right hw hA)

theorem actual_fold_16_error (g : ℕ→ℕ→ℝ) (y F R b c a z n m : ℕ)
    (hy : 2≤y) (hF : F=32*R) (hR : R∣oddWheel y)
    (A : ℝ) (hval : ∀ i j,0≤g i j ∧ g i j≤A) :
    |rectangle (fold g F (wheel y) b c) a z n m-
      (n:ℝ)*(m:ℝ)*mean (fold g F (wheel y) b c) 16|≤
      15*((n:ℝ)+(m:ℝ))*A :=
  rectangle_16_error _ (folded_period _ _ _ _ _ _ (period_16_divides hy hF hR))
    a z n m A (fun i j => hval _ _)

end ActualSquarefreeWheelConductor16318
