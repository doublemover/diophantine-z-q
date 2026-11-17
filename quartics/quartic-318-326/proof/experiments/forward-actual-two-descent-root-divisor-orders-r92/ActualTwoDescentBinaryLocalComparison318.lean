module
public import ActualTwoDescentUnitSquareNecessity318
public section
noncomputable section
namespace ActualTwoDescentBinaryLocalComparison318
open ActualTwoDescentUnitSquareNecessity318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

lemma actual_unit_valuation_zero (x : ℚ_[p]) (hn : ‖x‖=1) : x.valuation=0 := by
  have h1 := (Padic.norm_le_one_iff_val_nonneg x).mp hn.le
  have h2 : 0 ≤ (x⁻¹).valuation := (Padic.norm_le_one_iff_val_nonneg (x⁻¹)).mp
    (by rw [norm_inv,hn,inv_one])
  rw [Padic.valuation_inv] at h2
  omega

/-- Valuation parity and the actual stripped-unit symbol are invariants of
an ACTUAL local square relation. Both prime exponents are binary, so their
parity equality implies literal equality before canceling the prime power. -/
theorem actual_binary_local_comparison (e f : ZMod 2) (A D : ℤ)
    (hA : IsCoprime A (p : ℤ)) (hD : IsCoprime D (p : ℤ))
    (r : ℚ_[p]) (hr : r ≠ 0)
    (he : (p : ℚ_[p])^e.val*A=((p : ℚ_[p])^f.val*D)*r^2) :
    e=f ∧ jacobiSym A p=jacobiSym D p := by
  have hnA : ‖(A : ℚ_[p])‖=1 := Padic.norm_intCast_eq_one_iff.mpr hA
  have hnD : ‖(D : ℚ_[p])‖=1 := Padic.norm_intCast_eq_one_iff.mpr hD
  have hA0 : (A : ℚ_[p]) ≠ 0 := by intro h; rw [h,norm_zero] at hnA; norm_num at hnA
  have hD0 : (D : ℚ_[p]) ≠ 0 := by intro h; rw [h,norm_zero] at hnD; norm_num at hnD
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hvA := actual_unit_valuation_zero _ hnA
  have hvD := actual_unit_valuation_zero _ hnD
  have hv := congrArg Padic.valuation he
  rw [Padic.valuation_mul (pow_ne_zero _ hp0) hA0,
    Padic.valuation_mul (mul_ne_zero (pow_ne_zero _ hp0) hD0) (pow_ne_zero _ hr),
    Padic.valuation_mul (pow_ne_zero _ hp0) hD0,
    Padic.valuation_pow,Padic.valuation_pow,Padic.valuation_pow,
    Padic.valuation_p,hvA,hvD] at hv
  have heq : e=f := by
    have he2 := e.val_lt
    have hf2 := f.val_lt
    have hval : e.val=f.val := by omega
    exact ZMod.val_injective _ hval
  refine ⟨heq,?_⟩
  have hunit : (A : ℚ_[p])=(D : ℚ_[p])*r^2 := by
    rw [heq,mul_assoc] at he
    exact mul_left_cancel₀ (pow_ne_zero _ hp0) he
  exact actual_unit_square_comparison A D hA hD r hunit

/-- Compare two represented coordinates of the SAME actual local point.
The nonzero square multipliers are canceled in the completed field before
valuation or residue information is extracted. -/
theorem actual_binary_coordinate_comparison (x : ℚ_[p]) (e f : ZMod 2) (A D : ℤ)
    (hA : IsCoprime A (p : ℤ)) (hD : IsCoprime D (p : ℤ))
    (r s : ℚ_[p]) (hr : r ≠ 0) (hs : s ≠ 0)
    (hx : x=((p : ℚ_[p])^e.val*A)*r^2)
    (hy : x=((p : ℚ_[p])^f.val*D)*s^2) :
    e=f ∧ jacobiSym A p=jacobiSym D p := by
  apply actual_binary_local_comparison e f A D hA hD (s/r) (div_ne_zero hs hr)
  have he := hx.symm.trans hy
  apply (mul_right_cancel₀ (pow_ne_zero 2 hr))
  calc
    _=((p : ℚ_[p])^f.val*D)*s^2 := he
    _=(((p : ℚ_[p])^f.val*D)*(s/r)^2)*r^2 := by field_simp [hr]; ring

end ActualTwoDescentBinaryLocalComparison318
