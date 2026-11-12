module
public import ActualOriginalDyadicDensity318
public section
noncomputable section
namespace ActualOriginalAllPrimeFactors318
open Filter ActualFullLocalDensityRecurrence318 ActualLocalVolumeClosedForm318
open ActualOriginalLocalDensityLimit318 ActualOddBadLocalDensity318 ActualOriginalDyadicDensity318
open scoped Topology
set_option maxHeartbeats 24000000

lemma original_318_good_remaining (p : ℕ) (hp : p.Prime)
    (h2 : p≠2) (h3 : p≠3) (h53 : p≠53) : ¬(p:ℤ)∣318 := by
  intro hh
  have hd : p∣318 := by exact_mod_cast hh
  rw [show (318:ℕ)=2*3*53 by norm_num] at hd
  rcases hp.dvd_mul.mp hd with hd|hd
  · rcases hp.dvd_mul.mp hd with hd|hd
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
  · exact h53 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
lemma original_326_good_remaining (p : ℕ) (hp : p.Prime)
    (h2 : p≠2) (h163 : p≠163) : ¬(p:ℤ)∣326 := by
  intro hh
  have hd : p∣326 := by exact_mod_cast hh
  rw [show (326:ℕ)=2*163 by norm_num] at hd
  rcases hp.dvd_mul.mp hd with hd|hd
  · exact h2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)
  · exact h163 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd)

@[expose] def density318 (p : ℕ) : ℝ := by
  classical
  exact if p.Prime then if p=2 then 8/7 else if p=3 then 16/13 else if p=53 then 2916/2863
    else (localFactor p:ℝ) else 1
@[expose] def density326 (p : ℕ) : ℝ := by
  classical
  exact if p.Prime then if p=2 then 8/7 else if p=163 then 26896/26733
    else (localFactor p:ℝ) else 1

/-- EVERY finite prime of the literal318 quadric has an actual
original residue-count limit; no exceptional local input remains. -/
theorem actual_318_every_prime (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n : ℕ => (volume 318 p n:ℝ)) atTop (𝓝 (density318 p)) := by
  classical
  by_cases h2 : p=2
  · subst p
    simpa only [density318,if_pos (by norm_num : Nat.Prime 2),if_pos rfl] using original_318_at_two
  by_cases h3 : p=3
  · subst p
    norm_num [density318] at ⊢
    exact original_318_at_three
  by_cases h53 : p=53
  · subst p
    norm_num [density318] at ⊢
    exact original_318_at_fifty_three
  simpa only [density318,if_pos hp,if_neg h2,if_neg h3,if_neg h53] using
    actual_original_local_density_limit 318 p hp h2 (original_318_good_remaining p hp h2 h3 h53)

theorem actual_326_every_prime (p : ℕ) (hp : p.Prime) :
    Tendsto (fun n : ℕ => (volume 326 p n:ℝ)) atTop (𝓝 (density326 p)) := by
  classical
  by_cases h2 : p=2
  · subst p
    simpa only [density326,if_pos (by norm_num : Nat.Prime 2),if_pos rfl] using original_326_at_two
  by_cases h163 : p=163
  · subst p
    norm_num [density326] at ⊢
    exact original_326_at_one_sixty_three
  simpa only [density326,if_pos hp,if_neg h2,if_neg h163] using
    actual_original_local_density_limit 326 p hp h2 (original_326_good_remaining p hp h2 h163)

end ActualOriginalAllPrimeFactors318
