module
public import ActualGeometricLocalSeries318
public section
noncomputable section
namespace ActualOriginalLocalSeriesConvergence318
open ActualGeometricLocalSeries318 ActualFullLocalDensityRecurrence318
open ActualLocalVolumeClosedForm318 ActualOddBadLocalDensity318
open ActualOddBadLocalRecurrence318 ActualOriginalDyadicDensity318
open ActualOriginalAllPrimeFactors318
set_option maxHeartbeats 16000000

theorem good_prime_error_summable (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (h2 : p ≠ 2) (hκ : ¬(p : ℤ) ∣ κ) :
    Summable (fun n => ‖(volume κ p n : ℝ)-(localFactor p : ℝ)‖) := by
  apply parity_error_summable (fun n => (volume κ p n : ℝ)) (localFactor p : ℝ)
    (1-(localFactor p : ℝ)) (1-(localFactor p : ℝ)) (ratio p : ℝ)
  · unfold ratio
    positivity
  · exact_mod_cast ratio_lt_one p hp
  · intro n
    exact_mod_cast (actual_even_odd_formula κ p hp h2 hκ n).1
  · intro n
    exact_mod_cast (actual_even_odd_formula κ p hp h2 hκ n).2

theorem bad_prime_error_summable (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (h2 : p ≠ 2) (hκ : (p : ℤ) ∣ κ) (hκ2 : ¬(p : ℤ)^2 ∣ κ) :
    Summable (fun n => ‖(volume κ p n : ℝ)-(badFactor p : ℝ)‖) := by
  apply parity_error_summable (fun n => (volume κ p n : ℝ)) (badFactor p : ℝ)
    (1-(badFactor p : ℝ)) ((firstVolume p : ℝ)-(badFactor p : ℝ)) (ratio p : ℝ)
  · unfold ratio
    positivity
  · exact_mod_cast ratio_lt_one p hp
  · intro n
    exact_mod_cast (actual_bad_even_odd_formula κ p hp h2 hκ hκ2 n).1
  · intro n
    exact_mod_cast (actual_bad_even_odd_formula κ p hp h2 hκ hκ2 n).2

theorem dyadic_error_summable (κ : ℤ) (hκ : (2 : ℤ) ∣ κ)
    (hn4 : ¬(2 : ℤ)^2 ∣ κ) (h8 : (κ : ZMod 8) = 6)
    (h2 : (κ : ZMod 2) = 0) (h4 : (κ : ZMod 4) = 2) :
    Summable (fun n => ‖(volume κ 2 n : ℝ)-(8/7 : ℝ)‖) := by
  apply (summable_nat_add_iff 1).mp
  apply parity_error_summable (fun n => (volume κ 2 (n+1) : ℝ))
    (8/7) (1-8/7) (1-8/7) (1/8) (by norm_num) (by norm_num)
  · intro n
    exact_mod_cast (actual_original_dyadic_even_odd κ hκ hn4 h8 h2 h4 n).1
  · intro n
    have he : 2*n+1+1 = 2*n+2 := by omega
    rw [he]
    exact_mod_cast (actual_original_dyadic_even_odd κ hκ hn4 h8 h2 h4 n).2

/-- Every prime, including every exceptional place, has absolutely
summable error around a produced original local-count limit. -/
theorem original318_error_summable (p : ℕ) (hp : p.Prime) :
    ∃ S : ℝ, Summable (fun n => ‖(volume 318 p n : ℝ)-S‖) := by
  by_cases h2 : p = 2
  · subst p
    exact ⟨8/7,dyadic_error_summable 318 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)⟩
  by_cases h3 : p = 3
  · subst p
    exact ⟨badFactor 3,bad_prime_error_summable 318 3 hp (by norm_num)
      (by norm_num) (by norm_num)⟩
  by_cases h53 : p = 53
  · subst p
    exact ⟨badFactor 53,bad_prime_error_summable 318 53 hp (by norm_num)
      (by norm_num) (by norm_num)⟩
  exact ⟨localFactor p,good_prime_error_summable 318 p hp h2
    (original_318_good_remaining p hp h2 h3 h53)⟩

theorem original326_error_summable (p : ℕ) (hp : p.Prime) :
    ∃ S : ℝ, Summable (fun n => ‖(volume 326 p n : ℝ)-S‖) := by
  by_cases h2 : p = 2
  · subst p
    exact ⟨8/7,dyadic_error_summable 326 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)⟩
  by_cases h163 : p = 163
  · subst p
    exact ⟨badFactor 163,bad_prime_error_summable 326 163 hp (by norm_num)
      (by norm_num) (by norm_num)⟩
  exact ⟨localFactor p,good_prime_error_summable 326 p hp h2
    (original_326_good_remaining p hp h2 h163)⟩

@[expose] def originalLayers (κ : ℤ) (p : ℕ) : ℕ → ℝ :=
  layers (fun n => (volume κ p n : ℝ))

theorem actual318_local_layers (p : ℕ) (hp : p.Prime) :
    Summable (fun n => ‖originalLayers 318 p n‖) ∧
      HasSum (originalLayers 318 p) (density318 p) := by
  obtain ⟨S,hS⟩ := original318_error_summable p hp
  exact ⟨layers_summable_norm_of_error _ S hS,
    actual_layers_hasSum _ S _ hS (actual_318_every_prime p hp)⟩

theorem actual326_local_layers (p : ℕ) (hp : p.Prime) :
    Summable (fun n => ‖originalLayers 326 p n‖) ∧
      HasSum (originalLayers 326 p) (density326 p) := by
  obtain ⟨S,hS⟩ := original326_error_summable p hp
  exact ⟨layers_summable_norm_of_error _ S hS,
    actual_layers_hasSum _ S _ hS (actual_326_every_prime p hp)⟩

end ActualOriginalLocalSeriesConvergence318
