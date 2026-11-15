module
public import ActualOriginalLocalDensityLimit318
public section
noncomputable section
namespace ActualLocalPrimitiveNormalization318
open ActualLocalVolumeClosedForm318 ActualPrimitiveLocalVolume318
set_option maxHeartbeats 24000000

lemma actual_factor_explicit (p : ℕ) (hp : p.Prime) :
    localFactor p=1+1/((p:ℚ)*((p:ℚ)^2+p+1)) := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hd : 1-ratio p≠0 := ne_of_gt (sub_pos.mpr (ratio_lt_one p hp))
  have hpPos : (0:ℚ)<p := by exact_mod_cast hp.pos
  have hpoly : (p:ℚ)^2+p+1≠0 := ne_of_gt (by positivity)
  unfold localFactor
  apply (div_eq_iff hd).mpr
  unfold ratio
  field_simp [hp0,hpoly]
  <;> ring

theorem actual_factor_gt_one (p : ℕ) (hp : p.Prime) : 1<localFactor p := by
  rw [actual_factor_explicit p hp]
  have hpPos : (0:ℚ)<p := by exact_mod_cast hp.pos
  have hh : (0:ℚ)<1/((p:ℚ)*((p:ℚ)^2+p+1)) := by positivity
  linarith

theorem actual_factor_tail_bound (p : ℕ) (hp : p.Prime) :
    0<localFactor p-1 ∧ localFactor p-1≤1/(p:ℚ)^3 := by
  rw [actual_factor_explicit p hp]
  have hpPos : (0:ℚ)<p := by exact_mod_cast hp.pos
  have hpoly : (0:ℚ)<(p:ℚ)*((p:ℚ)^2+p+1) := by positivity
  have hp3 : (0:ℚ)<(p:ℚ)^3 := by positivity
  constructor
  · have hh := one_div_pos.mpr hpoly
    linarith
  · have hh : (1:ℚ)/((p:ℚ)*((p:ℚ)^2+p+1))≤1/(p:ℚ)^3 := by
      apply (div_le_div_iff₀ hpoly hp3).mpr
      nlinarith
    linarith

/-- Removing the genuine singular scaling tower gives exactly the
primitive factor. The exponent3 comes from FIVE singular digits and
FOUR-dimensional local normalization, not from a guessed zeta factor. -/
theorem actual_primitive_normalization (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    primitiveVolume κ p e=localFactor p*(1-ratio p) := by
  rw [actual_primitive_volume κ p hp hp2 hκ e]
  have hd : 1-ratio p≠0 := ne_of_gt (sub_pos.mpr (ratio_lt_one p hp))
  exact (div_mul_cancel₀ _ hd).symm

theorem actual_primitive_fraction (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    primitiveVolume κ p e/localFactor p=1-ratio p := by
  rw [actual_primitive_normalization κ p hp hp2 hκ e]
  have hs : localFactor p≠0 := ne_of_gt (lt_trans (by norm_num) (actual_factor_gt_one p hp))
  exact mul_div_cancel_left₀ _ hs

end ActualLocalPrimitiveNormalization318
