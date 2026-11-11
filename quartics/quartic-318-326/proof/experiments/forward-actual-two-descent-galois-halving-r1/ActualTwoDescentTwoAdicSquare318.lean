module
public import ActualTwoDescentJacobiPadicSquare318
public section
noncomputable section
namespace ActualTwoDescentTwoAdicSquare318
open ActualTwoDescentHenselSquare318
set_option maxHeartbeats 16000000

/-- The exact2-adic square criterion needed by the original17mod24 beta
and1mod24 theta products is proved by Hensel at1, with residual norm≤1/8
and derivative norm²=1/4. -/
theorem actual_two_adic_square (A : ℕ) (hA : (A : ZMod 8)=1) :
    ∃ r : ℚ_[2], r^2=(A : ℚ_[2]) := by
  have hres : (((1-(A : ℤ) : ℤ) : ZMod 8))=0 := by
    simp only [Int.cast_sub,Int.cast_one,Int.cast_natCast,hA,sub_self]
  have hdiv : (8 : ℤ) ∣ 1-(A : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp hres
  have hnorm : ‖(1 : ℤ_[2])^2-A‖ ≤ (2 : ℝ)^(-3 : ℤ) := by
    have h := (PadicInt.norm_int_le_pow_iff_dvd (p:=2) (k:=1-(A : ℤ)) (n:=3)).mpr
      (by norm_num only [show (2 : ℤ)^3=8 by norm_num]; exact hdiv)
    simpa only [Int.cast_sub,Int.cast_one,Int.cast_natCast,one_pow] using h
  have hderiv : ‖(2 : ℤ_[2])*1‖^2=(1/4 : ℝ) := by
    rw [mul_one,PadicInt.norm_p]
    norm_num
  obtain ⟨r,hr⟩ := actual_hensel_square (A : ℤ_[2]) 1 (by
    rw [hderiv]
    exact lt_of_le_of_lt hnorm (by norm_num))
  refine ⟨(r : ℚ_[2]),?_⟩
  exact_mod_cast hr

lemma actual_two_adic_square_of_mod24 (A : ℕ) (hA : (A : ZMod 24)=1 ∨ (A : ZMod 24)=17) :
    ∃ r : ℚ_[2], r^2=(A : ℚ_[2]) := by
  apply actual_two_adic_square A
  rcases hA with h | h
  · have he := congrArg (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)) h
    simpa only [map_natCast,map_one] using he
  · have he := congrArg (ZMod.castHom (by decide : 8 ∣ 24) (ZMod 8)) h
    norm_num only [map_natCast,map_ofNat] at he
    exact he

end ActualTwoDescentTwoAdicSquare318
