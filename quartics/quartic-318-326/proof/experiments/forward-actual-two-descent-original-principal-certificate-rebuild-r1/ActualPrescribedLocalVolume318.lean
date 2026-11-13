module
public import ActualPrimitiveLocalVolume318
public section
noncomputable section
namespace ActualPrescribedLocalVolume318
open QuadricCRTAssembly318 ActualPrimitivePrimePower318 ActualPrescribedPrimePower318
set_option maxHeartbeats 22000000

@[expose] def volume (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (R : Finset (Quadric (κ:ZMod m))) (e : ℕ) : ℚ :=
  ((levels κ m p R e).card:ℚ)/(modulus m p e:ℚ)^4

lemma modulus_fourth_scale (m p e : ℕ) :
    (modulus m p e:ℚ)^4=(m:ℚ)^4*((p:ℚ)^4)^e := by
  rw [modulus_eq,Nat.cast_mul,Nat.cast_pow,mul_pow]
  rw [←pow_mul,mul_comm e 4,pow_mul]

/-- Actual prescribed primitive residue volumes are invariant under
ALL genuine ambient lifts, from any initial modulus divisible by p. -/
theorem actual_prescribed_volume (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (hp : p.Prime) (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (hpm : p∣m)
    (R : Finset (Quadric (κ:ZMod m)))
    (hR : ∀x∈R,IsPrimitive κ m p x) (e : ℕ) :
    volume κ m p R e=(R.card:ℚ)/(m:ℚ)^4 := by
  have hm0 : (m:ℚ)≠0 := by exact_mod_cast NeZero.ne m
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast NeZero.ne p
  unfold volume
  rw [actual_prescribed_prime_power_count κ m p hp hp2 hκ hpm R hR e,modulus_fourth_scale]
  simp only [Nat.cast_mul,Nat.cast_pow]
  field_simp [hm0,hp0]

/-- Relative density of a fixed original prime-level condition is
unchanged at every higher level. The denominator is the ACTUAL full
primitive quadric, not an independent p^4 model. -/
theorem actual_prime_event_ratio (κ : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ)
    (R : Finset (Quadric (κ:ZMod p)))
    (hR : ∀x∈R,IsPrimitive κ p p x) (e : ℕ) :
    ((levels κ p p R e).card:ℚ)/(Nat.card (PrimitiveResidues κ (p^(e+1)) p):ℚ)=
      (R.card:ℚ)/((p^4-1:ℕ):ℚ) := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.ne_zero
  rw [actual_prescribed_prime_power_count κ p p hp hp2 hκ (dvd_refl p) R hR e,
    actual_primitive_prime_power_count κ p hp hp2 hκ e]
  simp only [Nat.cast_mul,Nat.cast_pow]
  exact mul_div_mul_right _ _ (pow_ne_zero e (pow_ne_zero 4 hp0))

/-- The arbitrary prescribed factor appearing in the analytic local
count is now identified with its actual finite-level preimages. This
is a local exact identity only, not the analytic integer-point count. -/
theorem actual_prescribed_real_volume (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (hp : p.Prime) (hp2 : p≠2) (hκ : ¬(p:ℤ)∣κ) (hpm : p∣m)
    (R : Finset (Quadric (κ:ZMod m)))
    (hR : ∀x∈R,IsPrimitive κ m p x) (e : ℕ) :
    (volume κ m p R e:ℝ)=(R.card:ℝ)/(m:ℝ)^4 := by
  rw [actual_prescribed_volume κ m p hp hp2 hκ hpm R hR e]
  norm_cast

end ActualPrescribedLocalVolume318
