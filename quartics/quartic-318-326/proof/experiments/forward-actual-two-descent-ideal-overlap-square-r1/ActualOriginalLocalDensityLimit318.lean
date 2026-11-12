module
public import ActualLocalVolumeClosedForm318
public section
noncomputable section
namespace ActualOriginalLocalDensityLimit318
open Filter ActualFullLocalDensityRecurrence318 ActualLocalVolumeClosedForm318
open scoped Topology
set_option maxHeartbeats 22000000

lemma original_half_exponent_tendsto : Tendsto (fun n : ℕ => n/2) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  exact eventually_atTop.2 ⟨2*b,fun n hn => by omega⟩

/-- The unrestricted local density is now a genuine limit of counts
on the SAME original quadric at every actual prime-power modulus. -/
theorem actual_original_local_density_limit (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) :
    Tendsto (fun n : ℕ => (volume κ p n:ℝ)) atTop (𝓝 (localFactor p:ℝ)) := by
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hr0 : (0:ℝ)≤(ratio p:ℝ) := by
    unfold ratio
    positivity
  have hr1 : (ratio p:ℝ)<1 := by exact_mod_cast ratio_lt_one p hp
  have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp original_half_exponent_tendsto
  have he (n : ℕ) : (volume κ p n:ℝ)=
      (localFactor p:ℝ)+(1-(localFactor p:ℝ))*(ratio p:ℝ)^(n/2) := by
    rw [actual_full_volume_formula κ p hp hp2 hκ n]
    simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_pow]
  simp_rw [he]
  simpa only [mul_zero,add_zero] using
    tendsto_const_nhds.add (tendsto_const_nhds.mul hg)

/-- Explicit displayed normalization of the same actual limit. -/
theorem actual_original_density_formula (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) :
    Tendsto (fun n : ℕ => (count κ p n:ℝ)/(p:ℝ)^(4*n)) atTop
      (𝓝 ((1-1/(p:ℝ)^4)/(1-1/(p:ℝ)^3))) := by
  have hh := actual_original_local_density_limit κ p hp hp2 hκ
  simpa only [volume,localFactor,ratio,Rat.cast_div,Rat.cast_sub,Rat.cast_one,
    Rat.cast_pow,Rat.cast_natCast] using hh

end ActualOriginalLocalDensityLimit318
