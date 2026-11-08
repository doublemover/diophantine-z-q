module
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic
public section
noncomputable section
namespace LocalHolomorphicSquareRoot318
open Filter Topology
set_option maxHeartbeats 0

lemma sqrt_square (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  rw [Complex.sqrt, ←Complex.cpow_nat_mul]
  norm_num

/-- Normalize to 1 before using the principal square root. This makes the
branch holomorphic near the chosen point even when f(a) lies on the branch cut. -/
@[expose] def root (f : ℂ → ℂ) (a b : ℂ) (z : ℂ) : ℂ :=
  b * Complex.sqrt (f z / f a)

lemma root_square (f : ℂ → ℂ) (a b : ℂ) (ha : f a ≠ 0) (hb : b^2=f a) (z : ℂ) :
    root f a b z ^ 2 = f z := by
  rw [root,mul_pow,sqrt_square,hb]
  exact mul_div_cancel₀ (f z) ha

lemma root_at (f : ℂ → ℂ) (a b : ℂ) (ha : f a ≠ 0) : root f a b a = b := by
  simp [root,ha]

lemma root_analyticAt (f : ℂ → ℂ) (a b : ℂ) (hf : AnalyticAt ℂ f a)
    (ha : f a ≠ 0) : AnalyticAt ℂ (root f a b) a := by
  have hs : AnalyticAt ℂ Complex.sqrt (1:ℂ) :=
    Complex.differentiableOn_sqrt.analyticOnNhd Complex.isOpen_slitPlane 1 (by simp)
  have hq : AnalyticAt ℂ (fun z => f z / f a) a := hf.div_const
  have hs' : AnalyticAt ℂ Complex.sqrt (f a/f a) := by simpa [ha] using hs
  exact analyticAt_const.mul (hs'.comp (f := fun z : ℂ => f z / f a) hq)

/-- A genuine holomorphic local square root through any specified nonzero
root, obtained explicitly rather than supplied as local trivialization data. -/
theorem exists_local_root (f : ℂ → ℂ) (a b : ℂ) (hf : AnalyticAt ℂ f a)
    (ha : f a ≠ 0) (hb : b^2=f a) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧ g a=b ∧ ∀ z, g z^2=f z :=
  ⟨root f a b,root_analyticAt f a b hf ha,root_at f a b ha,root_square f a b ha hb⟩

end LocalHolomorphicSquareRoot318
