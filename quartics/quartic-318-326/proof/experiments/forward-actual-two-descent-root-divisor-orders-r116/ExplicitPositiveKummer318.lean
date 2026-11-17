module
public import ActualTwoDescentKummerPointData318
public section
namespace ExplicitPositiveKummer318
open ActualTwoDescentPointExtraction318

/-- A constructed twist, not the twist selected by the prime-pattern machinery. -/
def parameter (β t : ℚ) : ℚ := β*(β-t^2)*(β-9*t^2)

lemma parameter_pos (β t : ℚ) (hb : 0<β) (ht : β<t^2) :
    0<parameter β t := by
  unfold parameter
  have ht0 : 0<t^2 := lt_trans hb ht
  exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hb (by linarith)) (by linarith)

/-- An explicit actual Kummer point. In particular the original squareclass
is supplied by coordinates, not inferred from a Selmer or local condition. -/
def point (β t : ℚ) (hb : 0<β) (ht : β<t^2) :
    KummerPoint β (parameter β t) where
  x := β*(β+3*t^2)^2
  y := β*(β+3*t^2)*(2*(β-3*t^2))*(4*β*t)
  u := 2*(β-3*t^2)
  v := 4*β*t
  x_ne := by positivity
  u_ne := by
    intro he
    have hs := sq_nonneg t
    nlinarith
  v_ne := by
    have htne : t≠0 := by intro he; subst t; norm_num at ht; linarith
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hb)) htne
  curve := by dsimp [parameter]; ring
  first := by dsimp [parameter]; ring
  second := by dsimp [parameter]; ring

/-- The constructed affine point is not an ordinate-zero point. No assertion about its order in the elliptic group is needed. -/
lemma ordinate_ne (β t : ℚ) (hb : 0<β) (ht : β<t^2) :
    (point β t hb ht).y≠0 := by
  change β*(β+3*t^2)*(2*(β-3*t^2))*(4*β*t)≠0
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (ne_of_gt hb) (by positivity)) (point β t hb ht).u_ne)
    (point β t hb ht).v_ne

lemma canonical_parameter_bound (β : ℚ) (hb : 0<β) : β<(β+1)^2 := by
  nlinarith [sq_nonneg β]

/-- Every positive rational beta has at least one positive twist with the
actual retained Kummer class represented. This does not select a common
successful twist for beta and beta-theta simultaneously. -/
theorem exists_positive_twist (β : ℚ) (hb : 0<β) :
    ∃ n : ℚ, 0<n ∧ Nonempty (KummerPoint β n) := by
  exact ⟨parameter β (β+1), parameter_pos β (β+1) hb (canonical_parameter_bound β hb),
    ⟨point β (β+1) hb (canonical_parameter_bound β hb)⟩⟩

end ExplicitPositiveKummer318
