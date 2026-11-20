module
public import ActualPureChartAxes318
public import Mathlib.Analysis.Calculus.FDeriv.Congr
import all ActualPureChartAxes318
public section
noncomputable section
namespace ActualOrderedChartJets318

open ActualPureChartAxes318
open scoped ContDiff Topology

/-- Ordered derivatives of the one actual chart. A word lists inner
derivatives first; no equality of differently ordered jets is asserted. -/
@[expose] def direction : Axis → Four
  | .z => (0,1,0,0)
  | .t => (0,0,1,0)
  | .v => (0,0,0,1)

@[expose] def step (a : Axis) (f : Four → ℂ) : Four → ℂ :=
  fun p => fderiv ℝ f p (direction a)

@[expose] def steps (a : Axis) : ℕ → (Four → ℂ) → (Four → ℂ)
  | 0, f => f
  | j+1, f => step a (steps a j f)

theorem step_smooth (a : Axis) {f : Four → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (step a f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem steps_smooth (a : Axis) {f : Four → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    ContDiff ℝ ∞ (steps a j f) := by
  induction j with
  | zero => exact hf
  | succ j ih => exact step_smooth a ih

theorem steps_zero_germ (a : Axis) {f : Four → ℂ} {p : Four}
    (h : f =ᶠ[𝓝 p] (fun _ => 0)) (j : ℕ) :
    steps a j f =ᶠ[𝓝 p] (fun _ => 0) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    have he := (ih.fderiv (𝕜 := ℝ)).fun_comp (fun L : Four →L[ℝ] ℂ => L (direction a))
    simpa [steps, step] using he

theorem point_line (a : Axis) (X : ℝ) (p : Outer) (s : ℝ) :
    HasDerivAt (point a X p) (direction a) s := by
  cases a
  · exact (hasDerivAt_const s X).prodMk ((hasDerivAt_id s).prodMk
      ((hasDerivAt_const s p.2).prodMk (hasDerivAt_const s p.1)))
  · exact (hasDerivAt_const s X).prodMk ((hasDerivAt_const s p.2).prodMk
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s p.1)))
  · exact (hasDerivAt_const s X).prodMk ((hasDerivAt_const s p.2).prodMk
      ((hasDerivAt_const s p.1).prodMk (hasDerivAt_id s)))

theorem step_line (a : Axis) (X : ℝ) (p : Outer) (s : ℝ)
    {f : Four → ℂ} (hf : ContDiff ℝ ∞ f) :
    HasDerivAt (fun t => f (point a X p t)) (step a f (point a X p s)) s :=
  ((hf.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt s (point_line a X p s)

theorem iterated_line (a : Axis) (X : ℝ) (p : Outer)
    {f : Four → ℂ} (hf : ContDiff ℝ ∞ f) (j : ℕ) :
    iteratedDeriv j (fun t => f (point a X p t)) =
      fun t => steps a j f (point a X p t) := by
  induction j with
  | zero => simp only [iteratedDeriv_zero, steps]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (step_line a X p t (steps_smooth a hf j)).deriv

/-- The signed rational seam is already zero on the open flat band in
the actual section. Every off-box ordered jet is zero by germ locality. -/
theorem actual_ordered_outside (κ τ : ℝ) (i : Fin 4) (a b : Axis) (m n : ℕ)
    (hτ : 0 < τ) {p : Four} (hp : p ∉ fullBox τ) :
    steps a m (steps b n (actual κ τ i)) p = 0 := by
  have hK : IsCompact (fullBox τ) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have h : actual κ τ i =ᶠ[𝓝 p] (fun _ => 0) := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hp] with u hu
    exact actual_outside hτ hu
  exact (steps_zero_germ a (steps_zero_germ b h n) m).eq_of_nhds

/-- All four original coordinates range simultaneously; J is chosen
before X, before Fourier frequencies and independently of the mesh. -/
theorem actual_ordered_uniform (κ τ : ℝ) (i : Fin 4) (a b : Axis) (m n : ℕ)
    (hτ : 0 < τ) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ p, ‖steps a m (steps b n (actual κ τ i)) p‖ ≤ J := by
  let f := steps a m (steps b n (actual κ τ i))
  have hK : IsCompact (fullBox τ) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hnon : (fullBox τ).Nonempty := ⟨(0,0,0,0),by
    simp only [fullBox,Set.mem_prod,mem_symmetric,abs_zero]
    exact ⟨by norm_num,by norm_num,by norm_num,by positivity⟩⟩
  have hc : Continuous (fun p => ‖f p‖) :=
    (steps_smooth a (steps_smooth b (actual_contDiff κ τ i) n) m).continuous.norm
  obtain ⟨v,_,hv⟩ := hK.exists_isMaxOn hnon hc.continuousOn
  refine ⟨max 1 ‖f v‖, le_max_left _ _, ?_⟩
  intro p
  change ‖f p‖ ≤ max 1 ‖f v‖
  by_cases hp : p ∈ fullBox τ
  · exact (hv hp).trans (le_max_right _ _)
  · rw [show f p = 0 from actual_ordered_outside κ τ i a b m n hτ hp, norm_zero]
    exact zero_le_one.trans (le_max_left _ _)

end ActualOrderedChartJets318
