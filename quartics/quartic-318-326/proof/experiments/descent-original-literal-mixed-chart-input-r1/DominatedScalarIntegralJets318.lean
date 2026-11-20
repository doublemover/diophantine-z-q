module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace DominatedScalarIntegralJets318
open MeasureTheory Set Filter
open scoped Topology ContDiff SchwartzMap

variable {α : Type*} [MeasurableSpace α]

/-- One scalar parameter, any integration space. In the chart the common
majorant is C_j times the indicator of a fixed bounded x or (x,y) box.
This is independent of whichever Fourier frequency is fixed at that step. -/
structure Jet (μ : Measure α) (F : ℕ → ℝ → α → ℂ) where
  integral : ∀ j x, Integrable (F j x) μ
  deriv : ∀ j x t,
    HasDerivAt (fun a => F j a t) (F (j+1) x t) x
  bound : ∀ j, ∃ b : α → ℝ, Integrable b μ ∧ ∀ x t, ‖F (j+1) x t‖≤b t

@[expose] def integrated (μ : Measure α) (F : ℕ → ℝ → α → ℂ) (j : ℕ) (x : ℝ) : ℂ :=
  ∫ t,F j x t ∂μ

theorem hasDerivAt_integrated {μ : Measure α} {F : ℕ → ℝ → α → ℂ}
    (J : Jet μ F) (j : ℕ) (x : ℝ) :
    HasDerivAt (integrated μ F j) (integrated μ F (j+1) x) x := by
  obtain ⟨b,hb,hbound⟩ := J.bound j
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := x) (F := F j) (F' := F (j+1)) (bound := b)
    Filter.univ_mem
    (Filter.Eventually.of_forall (fun y => (J.integral j y).aestronglyMeasurable))
    (J.integral j x) (J.integral (j+1) x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t y _ => hbound y t))
    hb
    (Filter.Eventually.of_forall (fun t y _ => J.deriv j y t))).2

theorem deriv_integrated {μ : Measure α} {F : ℕ → ℝ → α → ℂ}
    (J : Jet μ F) (j : ℕ) :
    deriv (integrated μ F j)=integrated μ F (j+1) :=
  funext (fun x => (hasDerivAt_integrated J j x).deriv)

theorem smooth_integrated {μ : Measure α} {F : ℕ → ℝ → α → ℂ}
    (J : Jet μ F) (j : ℕ) : ContDiff ℝ ∞ (integrated μ F j) := by
  have hd (k : ℕ) : Differentiable ℝ (integrated μ F k) :=
    fun x => (hasDerivAt_integrated J k x).differentiableAt
  have hfinite (n : ℕ) : ∀ k, ContDiff ℝ n (integrated μ F k) := by
    induction n with
    | zero =>
      intro k
      simpa only [Nat.cast_zero,contDiff_zero] using (hd k).continuous
    | succ n ih =>
      intro k
      rw [Nat.cast_succ,contDiff_succ_iff_deriv,deriv_integrated J k]
      refine ⟨hd k,?_,ih (k+1)⟩
      intro hω
      have hh : (n:ℕ∞ω)≠ω := by simp
      exact False.elim (hh hω)
  exact contDiff_infty.mpr (fun n => hfinite n j)

/-- The untransformed parameter support is the projected support of
the original integrand, independent of all Fourier parameters. -/
theorem support_integrated {μ : Measure α} {F : ℕ → ℝ → α → ℂ}
    (j : ℕ) (K : Set ℝ) (hK : IsCompact K)
    (hz : ∀ x∉K,∀ t,F j x t=0) :
    HasCompactSupport (integrated μ F j) := by
  have hs : Function.support (integrated μ F j) ⊆ K := by
    intro x hx
    by_contra h
    exact hx (by simp [integrated,hz x h])
  change IsCompact (closure (Function.support (integrated μ F j)))
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hs hK.isClosed)

def compactSchwartz {μ : Measure α} {F : ℕ → ℝ → α → ℂ}
    (J : Jet μ F) (j : ℕ) (K : Set ℝ) (hK : IsCompact K)
    (hz : ∀ x∉K,∀ t,F j x t=0) : 𝓢(ℝ,ℂ) :=
  (support_integrated j K hK hz).toSchwartzMap (smooth_integrated J j)

end DominatedScalarIntegralJets318
