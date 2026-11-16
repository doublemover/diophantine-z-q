module
public import ActualTwoDescentUniformLocalSquare318
public section
noncomputable section
namespace ActualTwoDescentLocalIdentityPoint318
open ActualTwoDescentUniformLocalSquare318 ActualTwoDescentGoodPrimeValuations318
open ActualTwoDescentTorsionSquarePairs318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- Construct an ACTUAL non-two-torsion Q_p point in the identity Kummer
class, for every prime including2 and3. The abscissa is a large square. -/
theorem actual_identity_local_point (n : ℕ) :
    ∃ P : LocalPoint (p:=p) n, SquarePair (P.x+3*n) (P.x-n) 1 1 := by
  obtain ⟨b,hb0,hb⟩ := actual_small_local_square (p:=p) ((1/4 : ℝ)/(‖(n : ℚ_[p])‖+1))
    (div_pos (by norm_num) (by positivity))
  have hsmall : ‖(n : ℚ_[p])‖*‖b^2‖ < (1/4 : ℝ) := by
    have hcross := (lt_div_iff₀ (by positivity : 0 < ‖(n : ℚ_[p])‖+1)).mp hb
    nlinarith [norm_nonneg (b^2)]
  let k : ℚ_[p] := b⁻¹
  let x : ℚ_[p] := k^2
  have hk : k ≠ 0 := inv_ne_zero hb0
  have hx : x ≠ 0 := pow_ne_zero 2 hk
  have hnratio : ‖(n : ℚ_[p])/x‖ < (1/4 : ℝ) := by
    rw [show (n : ℚ_[p])/x=n*b^2 by dsimp [x,k]; field_simp [hb0]; ring,norm_mul]
    exact hsmall
  have hAratio : ‖(x+3*n)/x-1‖ < (1/4 : ℝ) := by
    rw [show (x+3*n)/x-1=3*((n : ℚ_[p])/x) by field_simp [hx]; ring,norm_mul]
    have h3 : ‖(3 : ℚ_[p])‖ ≤ 1 := by simpa using Padic.norm_int_le_one (p:=p) 3
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) h3) hnratio
  have hBratio : ‖(x-n)/x-1‖ < (1/4 : ℝ) := by
    rw [show (x-n)/x-1= -((n : ℚ_[p])/x) by field_simp [hx]; ring,norm_neg]
    exact hnratio
  obtain ⟨r,hr,hA⟩ := actual_quarter_square _ hAratio
  obtain ⟨s,hs,hB⟩ := actual_quarter_square _ hBratio
  have hA' : x+3*n=x*r^2 := by rw [hA]; field_simp [hx] <;> ring
  have hB' : x-n=x*s^2 := by rw [hB]; field_simp [hx] <;> ring
  let P : LocalPoint (p:=p) n := {
    x := x
    y := k^3*r*s
    x_ne := hx
    minus_ne := by rw [hB']; exact mul_ne_zero hx (pow_ne_zero 2 hs)
    plus_ne := by rw [hA']; exact mul_ne_zero hx (pow_ne_zero 2 hr)
    curve := by rw [hA',hB']; dsimp [x]; ring }
  refine ⟨P,k*r,k*s,mul_ne_zero hk hr,mul_ne_zero hk hs,?_,?_⟩
  · change x+3*n=1*(k*r)^2
    rw [hA']; dsimp [x]; ring
  · change x-n=1*(k*s)^2
    rw [hB']; dsimp [x]; ring

end ActualTwoDescentLocalIdentityPoint318
