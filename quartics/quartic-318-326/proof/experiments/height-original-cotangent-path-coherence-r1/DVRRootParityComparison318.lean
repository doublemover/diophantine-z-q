module
public import OddTwistDilatationCoordinates318
public import IntegralValuativeRootCoordinates318
public section
noncomputable section
namespace DVRRootParityComparison318
set_option maxHeartbeats 1200000
variable (V K : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (pi : V) (hp : Irreducible pi)

/-- A unit times the SAME uniformizer is not a square in the actual
fraction field. Integral closure first descends the specified square root;
the odd-twist cancellation would then force the uniformizer to divide1. -/
theorem uniformizer_unit_not_square (u : Vˣ) (x : K)
    (hx : x^2=algebraMap V K ((u : V)*pi)) : False := by
  obtain ⟨z,hz,hz2⟩ := IntegralValuativeRootCoordinates318.square_preimage V K _ x hx
  have hd : pi ∣ (1 : V) := by
    have h := OddTwistDilatationCoordinates318.contact_difference_dvd pi hp u 0 1 z
      (by simpa only [sub_zero,mul_one] using hz2)
    simpa only [sub_zero] using h
  exact hp.not_isUnit (isUnit_of_dvd_one hd)

/-- One common nonzero factor cancels from the two actual root-square
identities; differing parity would construct the forbidden square above. -/
theorem odd_even_impossible (u v : Vˣ) (b : V) (hb : b≠0) (y z : K)
    (hy : y^2=algebraMap V K ((u : V)*pi*b))
    (hz : z^2=algebraMap V K ((v : V)*b)) : False := by
  have hv : algebraMap V K (v : V)≠0 := (v.isUnit.map (algebraMap V K)).ne_zero
  have hbK : algebraMap V K b≠0 := by
    simpa only [map_zero] using (IsFractionRing.injective V K).ne hb
  have hinv : algebraMap V K (v : V)*algebraMap V K (↑v⁻¹ : V)=1 := by
    rw [←map_mul,Units.mul_inv,map_one]
  apply uniformizer_unit_not_square V K pi hp (u*v⁻¹) (y/z)
  rw [div_pow,hy,hz]
  simp only [Units.val_mul,map_mul]
  apply (div_eq_iff (mul_ne_zero hv hbK)).2
  linear_combination -(algebraMap V K (u : V)*algebraMap V K pi*algebraMap V K b)*hinv

/-- The parity bits of two normalized twists with a common nonzero
factor MUST agree when both corresponding signed roots lie in the same
fraction field. No completeness or algebraic closure premise is used. -/
theorem parity_eq (u v : Vˣ) (b : V) (hb : b≠0) (e f : Fin 2) (y z : K)
    (hy : y^2=algebraMap V K ((u : V)*pi^(e : ℕ)*b))
    (hz : z^2=algebraMap V K ((v : V)*pi^(f : ℕ)*b)) : e=f := by
  fin_cases e <;> fin_cases f
  · rfl
  · exact False.elim (odd_even_impossible V K pi hp v u b hb z y
      (by simpa only [pow_one] using hz) (by simpa only [pow_zero,mul_one] using hy))
  · exact False.elim (odd_even_impossible V K pi hp u v b hb y z
      (by simpa only [pow_one] using hy) (by simpa only [pow_zero,mul_one] using hz))
  · rfl
end DVRRootParityComparison318
