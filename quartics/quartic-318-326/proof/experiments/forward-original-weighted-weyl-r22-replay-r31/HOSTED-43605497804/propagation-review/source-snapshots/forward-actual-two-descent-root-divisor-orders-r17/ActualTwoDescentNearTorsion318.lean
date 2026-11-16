module
public import ActualTwoDescentTorsionSquarePairs318
public section
noncomputable section
namespace ActualTwoDescentNearTorsion318
open ActualTwoDescentCloseSquare318 ActualTwoDescentTorsionSquarePairs318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

lemma actual_norm_three (hp3 : p ≠ 3) : ‖(3 : ℚ_[p])‖=1 :=
  Padic.norm_natCast_eq_one_iff.mpr
    ((Nat.coprime_primes Fact.out (by decide : Nat.Prime 3)).mpr hp3)
lemma actual_norm_four (hp2 : p ≠ 2) : ‖(4 : ℚ_[p])‖=1 := by
  have h2 : ‖(2 : ℚ_[p])‖=1 := Padic.norm_natCast_eq_one_iff.mpr
    ((Nat.coprime_primes Fact.out (by decide : Nat.Prime 2)).mpr hp2)
  rw [show (4 : ℚ_[p])=(2 : ℚ_[p])^2 by norm_num,norm_pow,h2,one_pow]

lemma actual_far_torsion (hp2 : p ≠ 2) (n x y : ℚ_[p])
    (hx : x ≠ 0) (hy : y ≠ 0) (hc : y^2=x*(x-n)*(x+3*n))
    (hfar : ‖n‖ < ‖x‖) : SquarePair (x+3*n) (x-n) 1 1 := by
  have hnratio : ‖n/x‖ < 1 := by rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hx)).mpr hfar
  have hAratio : ‖(x+3*n)/x-1‖ < 1 := by
    rw [show (x+3*n)/x-1=3*(n/x) by field_simp [hx]; ring,norm_mul]
    have h3 : ‖(3 : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p:=p) 3
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) h3) hnratio
  have hBratio : ‖(x-n)/x-1‖ < 1 := by
    rw [show (x-n)/x-1= -(n/x) by field_simp [hx]; ring,norm_neg]
    exact hnratio
  obtain ⟨r,hr,hA⟩ := actual_close_one_square hp2 _ hAratio
  obtain ⟨s,hs,hB⟩ := actual_close_one_square hp2 _ hBratio
  exact actual_identity_pair n x y r s hx hr hs hy hc hA hB

lemma actual_zero_torsion (hp2 : p ≠ 2) (hp3 : p ≠ 3) (n x : ℚ_[p])
    (hn : n ≠ 0) (hnear : ‖x‖ < ‖n‖) : SquarePair (x+3*n) (x-n) (3*n) (-n) := by
  have hAratio : ‖(x+3*n)/(3*n)-1‖ < 1 := by
    rw [show (x+3*n)/(3*n)-1=x/(3*n) by field_simp [hn]; ring,norm_div,norm_mul,
      actual_norm_three hp3,one_mul]
    exact (div_lt_one (norm_pos_iff.mpr hn)).mpr hnear
  have hBratio : ‖(x-n)/(-n)-1‖ < 1 := by
    rw [show (x-n)/(-n)-1=x/(-n) by field_simp [hn]; ring,norm_div,norm_neg]
    exact (div_lt_one (norm_pos_iff.mpr hn)).mpr hnear
  obtain ⟨r,hr,hA⟩ := actual_close_one_square hp2 _ hAratio
  obtain ⟨s,hs,hB⟩ := actual_close_one_square hp2 _ hBratio
  refine ⟨r,s,hr,hs,?_,?_⟩
  · rw [hA]; field_simp [hn] <;> ring
  · rw [hB]; field_simp [hn] <;> ring

lemma actual_positive_torsion (hp2 : p ≠ 2) (n x y : ℚ_[p])
    (hn : n ≠ 0) (hy : y ≠ 0) (hc : y^2=x*(x-n)*(x+3*n))
    (hnear : ‖x-n‖ < ‖n‖) : SquarePair (x+3*n) (x-n) n 1 := by
  have hxratio : ‖x/n-1‖ < 1 := by
    rw [show x/n-1=(x-n)/n by field_simp [hn]; ring,norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hn)).mpr hnear
  have hAratio : ‖(x+3*n)/(4*n)-1‖ < 1 := by
    rw [show (x+3*n)/(4*n)-1=(x-n)/(4*n) by field_simp [hn]; ring,norm_div,norm_mul,
      actual_norm_four hp2,one_mul]
    exact (div_lt_one (norm_pos_iff.mpr hn)).mpr hnear
  obtain ⟨r,hr,hx⟩ := actual_close_one_square hp2 _ hxratio
  obtain ⟨s,hs,hA⟩ := actual_close_one_square hp2 _ hAratio
  exact actual_first_torsion_pair n x y r s hn hr hs hy hc hx hA

lemma actual_negative_torsion (hp2 : p ≠ 2) (hp3 : p ≠ 3) (n x y : ℚ_[p])
    (hn : n ≠ 0) (hy : y ≠ 0) (hc : y^2=x*(x-n)*(x+3*n))
    (hnear : ‖x+3*n‖ < ‖n‖) : SquarePair (x+3*n) (x-n) 3 (-n) := by
  have hxratio : ‖x/(-3*n)-1‖ < 1 := by
    rw [show x/(-3*n)-1=(x+3*n)/(-3*n) by field_simp [hn]; ring,norm_div,norm_mul,norm_neg,
      actual_norm_three hp3,one_mul]
    exact (div_lt_one (norm_pos_iff.mpr hn)).mpr hnear
  have hBratio : ‖(x-n)/(-4*n)-1‖ < 1 := by
    rw [show (x-n)/(-4*n)-1=(x+3*n)/(-4*n) by field_simp [hn]; ring,norm_div,norm_mul,norm_neg,
      actual_norm_four hp2,one_mul]
    exact (div_lt_one (norm_pos_iff.mpr hn)).mpr hnear
  obtain ⟨r,hr,hx⟩ := actual_close_one_square hp2 _ hxratio
  obtain ⟨s,hs,hB⟩ := actual_close_one_square hp2 _ hBratio
  exact actual_second_torsion_pair n x y r s hn hr hs hy hc hx hB

end ActualTwoDescentNearTorsion318
