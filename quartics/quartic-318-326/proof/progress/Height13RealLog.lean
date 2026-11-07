module
public import QuarticOptimization
public section
namespace Height13RealLog
@[expose] noncomputable def J1 (x : ℝ) : ℝ := 1-x/5
@[expose] noncomputable def J8 (x : ℝ) : ℝ :=
  1-x/5+x^2/15-x^3/39+7*x^4/663-x^5/221+11*x^6/5525-
    11*x^7/12325+x^8/2465

theorem J1_lower (x : ℝ) (hx : x ≤ 0) : 1 ≤ J1 x := by
  unfold J1
  linarith

theorem J8_lower (x : ℝ) (hx : x ≤ 0) : 1 ≤ J8 x := by
  let u := -x
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have heq : x = -u := by dsimp [u]; ring
  rw [heq]
  have hh : 0 ≤ J8 (-u)-1 := by
    unfold J8
    ring_nf
    positivity
  linarith

theorem J1_nonzero (x : ℝ) (hx : x ≤ 0) : J1 x ≠ 0 := by
  have := J1_lower x hx
  linarith

theorem J8_nonzero (x : ℝ) (hx : x ≤ 0) : J8 x ≠ 0 := by
  have := J8_lower x hx
  linarith

theorem log_zero_iff (u delta : ℝ) (hd : delta ≤ 0) :
    -u*J8 delta=0 ↔ u=0 := by
  simp only [mul_eq_zero,neg_eq_zero,J8_nonzero delta hd,or_false]

end Height13RealLog
