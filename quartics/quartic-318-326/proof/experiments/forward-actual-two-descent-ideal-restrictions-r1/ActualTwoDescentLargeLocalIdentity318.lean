module
public import ActualTwoDescentOriginalAllPlacesProducer318
public section
noncomputable section
namespace ActualTwoDescentLargeLocalIdentity318
open ActualTwoDescentUniformLocalSquare318 ActualTwoDescentGoodPrimeValuations318
open ActualTwoDescentTorsionSquarePairs318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- Construct an ACTUAL non-two-torsion Q_p point in the identity Kummer
class, for every prime including2 and3. The abscissa is a large square. -/
theorem actual_large_identity_local_point (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ P : LocalPoint (p:=p) n, SquarePair (P.x+3*n) (P.x-n) 1 1 ∧ M < ‖P.x‖ := by
  obtain ⟨b,hb0,hbmin⟩ := actual_small_local_square (p:=p)
    (min ((1/4 : ℝ)/(‖(n : ℚ_[p])‖+1)) (1/(M+1)))
    (lt_min (div_pos (by norm_num) (by positivity)) (div_pos one_pos (by positivity)))
  have hb : ‖b^2‖ < (1/4 : ℝ)/(‖(n : ℚ_[p])‖+1) := lt_of_lt_of_le hbmin (min_le_left _ _)
  have hbM : ‖b^2‖ < 1/(M+1) := lt_of_lt_of_le hbmin (min_le_right _ _)
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
  have hbound : M < ‖P.x‖ := by
    change M < ‖x‖
    have hxinv : x=(b^2)⁻¹ := by simp only [x,k,inv_pow]
    rw [hxinv,norm_inv]
    change M < 1/‖b^2‖
    apply (lt_div_iff₀ (norm_pos_iff.mpr (pow_ne_zero 2 hb0))).mpr
    have hbM' := (lt_div_iff₀ (by positivity : 0 < M+1)).mp hbM
    nlinarith [norm_pos_iff.mpr (pow_ne_zero 2 hb0)]
  refine ⟨P,⟨k*r,k*s,mul_ne_zero hk hr,mul_ne_zero hk hs,?_,?_⟩,hbound⟩
  · change x+3*n=1*(k*r)^2
    rw [hA']; dsimp [x]; ring
  · change x-n=1*(k*s)^2
    rw [hB']; dsimp [x]; ring

end ActualTwoDescentLargeLocalIdentity318
