module
public import ActualTwoDescentLocalIdentityPoint318
public section
noncomputable section
namespace ActualTwoDescentLocalFirstTorsionPoint318
open ActualTwoDescentUniformLocalSquare318 ActualTwoDescentGoodPrimeValuations318
open ActualTwoDescentTorsionSquarePairs318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- Construct an ACTUAL non-two-torsion Q_p point in the first torsion
Kummer class for every prime, including2 and3. The abscissa is n+b² with
b nonzero and sufficiently small; the ordinate is constructed explicitly. -/
theorem actual_first_torsion_local_point (n : ℕ) (hn0 : n ≠ 0) :
    ∃ P : LocalPoint (p:=p) n, SquarePair (P.x+3*n) (P.x-n) (n : ℚ_[p]) 1 := by
  have hn : (n : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have h4n : 4*(n : ℚ_[p]) ≠ 0 := mul_ne_zero (by norm_num) hn
  obtain ⟨b,hb0,hb⟩ := actual_small_local_square (p:=p) (‖4*(n : ℚ_[p])‖/4)
    (div_pos (norm_pos_iff.mpr h4n) (by norm_num))
  have hbn : ‖b^2‖ < ‖(n : ℚ_[p])‖/4 := by
    have h4 : ‖(4 : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p:=p) 4
    apply lt_of_lt_of_le hb
    rw [norm_mul]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) h4) (by norm_num)
  let x : ℚ_[p] := n+b^2
  have hB : x-n=b^2 := by dsimp [x]; ring
  have hxratio : ‖x/n-1‖ < (1/4 : ℝ) := by
    rw [show x/(n : ℚ_[p])-1=b^2/n by dsimp [x]; field_simp [hn]; ring,norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr hn)).mpr
    nlinarith [hbn]
  have hAratio : ‖(x+3*n)/(4*n)-1‖ < (1/4 : ℝ) := by
    rw [show (x+3*n)/(4*n)-1=b^2/(4*n) by dsimp [x]; field_simp [hn]; ring,norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr h4n)).mpr
    nlinarith [hb]
  obtain ⟨r,hr,hx⟩ := actual_quarter_square _ hxratio
  obtain ⟨s,hs,hA⟩ := actual_quarter_square _ hAratio
  have hx' : x=(n : ℚ_[p])*r^2 := by rw [hx]; field_simp [hn] <;> ring
  have hA' : x+3*n=4*n*s^2 := by rw [hA]; field_simp [hn] <;> ring
  let P : LocalPoint (p:=p) n := {
    x := x
    y := 2*n*b*r*s
    x_ne := by rw [hx']; exact mul_ne_zero hn (pow_ne_zero 2 hr)
    minus_ne := by rw [hB]; exact pow_ne_zero 2 hb0
    plus_ne := by rw [hA']; exact mul_ne_zero h4n (pow_ne_zero 2 hs)
    curve := by rw [hB,hA',hx']; ring }
  refine ⟨P,2*s,b,mul_ne_zero (by norm_num) hs,hb0,?_,?_⟩
  · change x+3*n=(n : ℚ_[p])*(2*s)^2
    rw [hA']; ring
  · change x-n=1*b^2
    simpa only [one_mul] using hB

end ActualTwoDescentLocalFirstTorsionPoint318
