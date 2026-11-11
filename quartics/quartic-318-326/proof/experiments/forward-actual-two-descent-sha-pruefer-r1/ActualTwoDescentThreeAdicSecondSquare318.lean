module
public import ActualTwoDescentLocalValuationTools318
public section
noncomputable section
namespace ActualTwoDescentThreeAdicSecondSquare318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentCloseSquare318
set_option maxHeartbeats 16000000

/-- Every actual non-two-torsion local point at3 has SQUARE second Kummer
coordinate. The square root is constructed from the cubic, not assumed as
a local-image condition. -/
theorem actual_three_second_square (n : ℕ) (hn : (n : ZMod 3)=2)
    (P : LocalPoint (p:=3) n) : ∃ v : ℚ_[3], v ≠ 0 ∧ v^2=P.x-n := by
  have hn0 : n ≠ 0 := by intro he; norm_num [he] at hn
  have hnc : (n : ℚ_[3]) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hnunit : ‖(n : ℚ_[3])‖=1 := by
    apply Padic.norm_natCast_eq_one_iff.mpr
    apply Nat.Coprime.symm
    apply (ZMod.isUnit_iff_coprime n 3).mp
    rw [hn]
    exact (ZMod.unitOfCoprime 2 (by decide)).isUnit
  have hdiv : 3 ∣ n+1 := by
    apply (ZMod.natCast_eq_zero_iff (n+1) 3).mp
    rw [Nat.cast_add,Nat.cast_one,hn]
    norm_num
  have hneg : ‖(-(n : ℚ_[3]))-1‖ < 1 := by
    rw [show (-(n : ℚ_[3]))-1= -((n+1 : ℕ) : ℚ_[3]) by push_cast; ring,norm_neg]
    exact Padic.norm_natCast_lt_one_iff.mpr hdiv
  have hy : P.y ≠ 0 := by
    intro he
    have h := P.curve
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact (mul_ne_zero (mul_ne_zero P.x_ne P.minus_ne) P.plus_ne) h.symm
  by_cases hx : ‖P.x‖ < 1
  · have hratio : ‖(P.x-n)/(-n)-1‖ < 1 := by
      rw [show (P.x-n)/(-n)-1=P.x/(-n) by field_simp [hnc]; ring,norm_div,norm_neg,hnunit,div_one]
      exact hx
    obtain ⟨r,hr,he⟩ := actual_close_one_square (p:=3) (by decide) _ hratio
    obtain ⟨s,hs,hsq⟩ := actual_close_one_square (p:=3) (by decide) _ hneg
    refine ⟨r*s,mul_ne_zero hr hs,?_⟩
    rw [mul_pow,he,hsq]
    field_simp [hnc]
  · have hratio : ‖(P.x+3*n)/P.x-1‖ < 1 := by
      rw [show (P.x+3*n)/P.x-1=(3*(n : ℚ_[3]))/P.x by field_simp [P.x_ne]; ring,
        norm_div,norm_mul,hnunit,mul_one]
      apply (div_lt_one (norm_pos_iff.mpr P.x_ne)).mpr
      exact lt_of_lt_of_le Padic.norm_p_lt_one (le_of_not_gt hx)
    obtain ⟨r,hr,he⟩ := actual_close_one_square (p:=3) (by decide) _ hratio
    have hA : P.x+3*n=P.x*r^2 := by rw [he]; field_simp [P.x_ne] <;> ring
    refine ⟨P.y/(P.x*r),div_ne_zero hy (mul_ne_zero P.x_ne hr),?_⟩
    rw [div_pow,P.curve,hA]
    field_simp [P.x_ne,hr]
    <;> ring

end ActualTwoDescentThreeAdicSecondSquare318
