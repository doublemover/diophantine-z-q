module
public import ConcreteQuadraticDomains
public section
namespace NormChainZero
variable {K : Type*} [Field K]

/-- A single anisotropic norm step cannot kill a nonzero previous value. -/
theorem step_nonzero (q previous leaf : K)
    (hq : ¬ ∃ s : K, s^2 = -q) (hp : previous ≠ 0) :
    previous^2+q*leaf^2 ≠ 0 := by
  intro h
  have hl : leaf ≠ 0 := by
    intro hz
    have hp2 : previous^2=0 := by simpa [hz] using h
    exact (pow_ne_zero 2 hp) hp2
  apply hq
  refine ⟨previous/leaf, ?_⟩
  field_simp [hl]
  linear_combination h

theorem fold_nonzero (q : K) (leaves : List K) (initial : K)
    (hq : ¬ ∃ s : K, s^2 = -q) (hi : initial ≠ 0) :
    leaves.foldl (fun previous leaf => previous^2+q*leaf^2) initial ≠ 0 := by
  induction leaves generalizing initial with
  | nil => simpa using hi
  | cons head tail ih =>
    simp only [List.foldl_cons]
    exact ih _ (step_nonzero q initial head hq hi)

theorem zero_implies_negative_square (q : K) (leaves : List K)
    (hzero : leaves.foldl (fun previous leaf => previous^2+q*leaf^2) 1 = 0) :
    ∃ s : K, s^2 = -q := by
  by_contra h
  exact fold_nonzero q leaves 1 h one_ne_zero hzero


theorem degenerate_trace (w0 w1 n : ℚ)
    (h : 2*w0*n=w0^2-2*w1^2) (hz : w0=0) : w1=0 := by
  rw [hz] at h
  have hs : w1^2=0 := by nlinarith
  exact (sq_eq_zero_iff).mp hs


theorem nondegenerate_trace_domains (w0 w1 n : ℚ)
    (h : 2*w0*n=w0^2-2*w1^2) (hw : ¬ (w0=0 ∧ w1=0)) :
    w0 ≠ 0 ∧ n ≠ 0 := by
  have hw0 : w0 ≠ 0 := by
    intro hz
    exact hw ⟨hz,degenerate_trace w0 w1 n h hz⟩
  refine ⟨hw0, ?_⟩
  intro hn
  apply ConcreteQuadraticDomains.norm_nonzero_of_real_nonzero w0 w1 hw0
  rw [hn] at h
  linear_combination -h

end NormChainZero
