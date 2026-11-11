module
public import ActualPrescribedPrimePower318
public section
noncomputable section
namespace ActualPrimitiveLocalVolume318
open ActualPrimitivePrimePower318
set_option maxHeartbeats 20000000

/-- Normalization is by the actual four-dimensional residue scale. -/
@[expose] def primitiveVolume (κ : ℤ) (p e : ℕ) : ℚ :=
  (Nat.card (PrimitiveResidues κ (p^(e+1)) p):ℚ)/(p^(e+1):ℚ)^4

lemma power_scale (a : ℚ) (e : ℕ) : (a^(e+1))^4=a^4*(a^4)^e := by
  rw [pow_succ a e,mul_pow]
  rw [←pow_mul, mul_comm e 4,pow_mul,mul_comm]

/-- The primitive local density is EXACTLY constant at every finite
level, not obtained by exchanging a limit with a counting argument. -/
theorem actual_primitive_volume (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    primitiveVolume κ p e=1-1/(p:ℚ)^4 := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  have hp4 : 1≤p^4 := one_le_pow₀ (show 1≤p by omega)
  unfold primitiveVolume
  rw [actual_primitive_prime_power_count κ p hp hp2 hκ e]
  simp only [Nat.cast_mul,Nat.cast_sub hp4,Nat.cast_one,Nat.cast_pow]
  rw [power_scale]
  field_simp [hp0]
  <;> ring

theorem actual_primitive_volume_pos (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    0 < primitiveVolume κ p e := by
  rw [actual_primitive_volume κ p hp hp2 hκ e]
  have hp1 : (1:ℚ)<p := by exact_mod_cast hp.one_lt
  have h2 : (1:ℚ)<(p:ℚ)^2 := by nlinarith [sq_nonneg ((p:ℚ)-1)]
  have h4 : (1:ℚ)<(p:ℚ)^4 := by nlinarith [sq_nonneg ((p:ℚ)^2-1)]
  have hpos : (0:ℚ)<(p:ℚ)^4 := lt_trans (by norm_num) h4
  have hh : (1:ℚ)/(p:ℚ)^4<1 := (div_lt_one hpos).mpr h4
  linarith

/-- The local primitive factor used in the global sieve is the same
actual finite-level count, with no rescaling of the original quadric. -/
theorem original_local_factor (κ : ℤ) (p : ℕ) (hp : p.Prime)
    (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (e : ℕ) :
    (primitiveVolume κ p e:ℝ)=1-1/(p:ℝ)^4 := by
  rw [actual_primitive_volume κ p hp hp2 hκ e]
  norm_cast

end ActualPrimitiveLocalVolume318
