module
public import ActualTwoDescentTwoAdicSquare318
public section
noncomputable section
namespace ActualTwoDescentThreeAdicTorsion318
open ActualTwoDescentHenselSquare318
set_option maxHeartbeats 16000000

lemma actual_three_adic_one_square (A : ℕ) (hA : (A : ZMod 3)=1) :
    ∃ r : ℚ_[3], r^2=(A : ℚ_[3]) := by
  have he : (((1-(A : ℤ) : ℤ) : ZMod 3))=0 := by
    simp only [Int.cast_sub,Int.cast_one,Int.cast_natCast,hA,sub_self]
  have hdiv : (3 : ℤ) ∣ (1 : ℤ)^2-A := by
    simpa only [one_pow] using (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp he
  obtain ⟨r,hr⟩ := actual_odd_square_lift (p:=3) (by decide) A 1 (by simp) hdiv
  exact ⟨(r : ℚ_[3]),by exact_mod_cast hr⟩

/-- For both actual twists11mod12, beta17mod24 differs from the first
torsion coordinate by an actual nonzero square in Q_3. -/
theorem actual_beta_three_torsion (β n : ℕ) (hn0 : n ≠ 0)
    (hβ : (β : ZMod 24)=17) (hn : (n : ZMod 12)=11) :
    ∃ r : ℚ_[3], r ≠ 0 ∧ (β : ℚ_[3])=(n : ℚ_[3])*r^2 := by
  have hβ3 : (β : ZMod 3)=2 := by
    have h := congrArg (ZMod.castHom (by decide : 3 ∣ 24) (ZMod 3)) hβ
    norm_num only [map_natCast,map_ofNat] at h
    exact h
  have hn3 : (n : ZMod 3)=2 := by
    have h := congrArg (ZMod.castHom (by decide : 3 ∣ 12) (ZMod 3)) hn
    norm_num only [map_natCast,map_ofNat] at h
    exact h
  have hprod : ((β*n : ℕ) : ZMod 3)=1 := by
    rw [Nat.cast_mul,hβ3,hn3]
    norm_num
  obtain ⟨s,hs⟩ := actual_three_adic_one_square (β*n) hprod
  have hnc : (n : ℚ_[3]) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hβ0 : β ≠ 0 := by
    intro he
    rw [he,Nat.cast_zero] at hβ3
    norm_num at hβ3
  have hs0 : s ≠ 0 := by
    intro he
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
    exact (Nat.cast_ne_zero.mpr (mul_ne_zero hβ0 hn0)) hs.symm
  refine ⟨s/n,div_ne_zero hs0 hnc,?_⟩
  rw [div_pow,hs,Nat.cast_mul]
  field_simp [hnc]
  <;> ring

end ActualTwoDescentThreeAdicTorsion318
