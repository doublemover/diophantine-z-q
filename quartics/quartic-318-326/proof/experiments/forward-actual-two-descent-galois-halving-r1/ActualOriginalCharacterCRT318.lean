module
public import ActualOriginalFrequencyCRT318
public section
noncomputable section
namespace ActualOriginalCharacterCRT318
open QuadricCRTAssembly318 ActualOriginalFrequencyCRT318
set_option maxHeartbeats 16000000

/-- Explicit standard-character normalization under a divisor ring
map. The quotient multiplier k and q=d*k are retained in the statement. -/
lemma actual_scaled_character (q d k : ℕ) [NeZero q] [NeZero d] [NeZero k]
    (hq : q=d*k) (φ : ZMod q →+* ZMod d) (z : ZMod q) :
    ZMod.stdAddChar ((k : ZMod q)*z) = ZMod.stdAddChar (φ z) := by
  have hi (a : ℤ) : ZMod.stdAddChar ((k*a : ℤ) : ZMod q) =
      ZMod.stdAddChar (a : ZMod d) := by
    rw [ZMod.stdAddChar_coe,ZMod.stdAddChar_coe,hq]
    congr 1
    have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
    have hd : (d : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
    push_cast
    field_simp [hk,hd]
    <;> ring
  have hz := hi (z.val : ℤ)
  have hφ : φ z = (z.val : ZMod d) := by
    have h := congrArg φ (ZMod.natCast_zmod_val z)
    simpa only [map_natCast] using h.symm
  rw [hφ]
  simpa only [Int.cast_mul,Int.cast_natCast,ZMod.natCast_zmod_val] using hz

/-- Character CRT for the literal original equation, using the
cross-scaled frequency bijection and the unscaled original residue CRT. -/
theorem actual_original_crt_phase (κ : ℤ) (m n : ℕ) [NeZero m] [NeZero n]
    (h : m.Coprime n) (a : ZMod m) (b : ZMod n) (x : Coordinates (ZMod (m*n))) :
    ZMod.stdAddChar (frequencyMerge m n h (a,b)*equation (κ : ZMod (m*n)) x) =
      ZMod.stdAddChar (a*equation (κ : ZMod m) ((residueCRT m n h x).1)) *
        ZMod.stdAddChar (b*equation (κ : ZMod n) ((residueCRT m n h x).2)) := by
  rw [actual_frequency_merge_formula,add_mul,AddChar.map_add_eq_mul]
  rw [mul_assoc,mul_assoc]
  rw [actual_scaled_character (m*n) m n rfl (first m n h),
    actual_scaled_character (m*n) n m (Nat.mul_comm m n) (second m n h)]
  simp only [map_mul,map_natCast,ZMod.natCast_zmod_val,←equation_map,map_intCast,
    actual_residue_crt_first,actual_residue_crt_second]

end ActualOriginalCharacterCRT318
