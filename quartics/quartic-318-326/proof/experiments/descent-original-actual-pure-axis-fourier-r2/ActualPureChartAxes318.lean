module
public import ActualTubeChartSupport318
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public section
noncomputable section
namespace ActualPureChartAxes318
open MeasureTheory
open scoped ContDiff Topology
open ActualTubeAnnulusChart318 ActualTubeChartSupport318

inductive Axis where
  | z
  | t
  | v
  deriving DecidableEq
abbrev Outer := ℝ×ℝ
abbrev Four := ℝ×ℝ×ℝ×ℝ

/-- All three rows are in the original normalized physical axes.
Outer pairs: Z inner -> (V,T), T inner -> (V,Z), V inner -> (T,Z). -/
@[expose] def point (axis : Axis) (X : ℝ) (p : Outer) (s : ℝ) : Four :=
  match axis with
  | .z => (X,s,p.2,p.1)
  | .t => (X,p.2,s,p.1)
  | .v => (X,p.2,p.1,s)

def dir (axis : Axis) : Four :=
  match axis with
  | .z => (0,1,0,0)
  | .t => (0,0,1,0)
  | .v => (0,0,0,1)

@[expose] def rowR (axis : Axis) (τ : ℝ) : ℝ :=
  match axis with | .v => 2*τ | _ => 4
@[expose] def outerR₁ (axis : Axis) (τ : ℝ) : ℝ :=
  match axis with | .v => 4 | _ => 2*τ

def symmetric (r : ℝ) : Set ℝ := Set.Icc (-r) r

lemma mem_symmetric {r u : ℝ} : u∈symmetric r ↔ |u|≤r := by
  rw [symmetric,Set.mem_Icc,abs_le]

def outerBox (axis : Axis) (τ : ℝ) : Set Outer :=
  symmetric (outerR₁ axis τ) ×ˢ symmetric 4

def fullBox (τ : ℝ) : Set Four :=
  symmetric 4 ×ˢ (symmetric 4 ×ˢ (symmetric 4 ×ˢ symmetric (2*τ)))

theorem outerBox_compact (axis : Axis) (τ : ℝ) : IsCompact (outerBox axis τ) :=
  isCompact_Icc.prod isCompact_Icc

private theorem fullBox_compact (τ : ℝ) : IsCompact (fullBox τ) :=
  isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))

theorem point_in_box (axis : Axis) (τ X : ℝ) (p : Outer) (s : ℝ) :
    point axis X p s∈fullBox τ ↔ |X|≤4 ∧ p∈outerBox axis τ ∧ |s|≤rowR axis τ := by
  cases axis <;>
    simp only [point,fullBox,outerBox,Set.mem_prod,mem_symmetric,rowR,outerR₁] <;> tauto

@[expose] def actual (κ τ : ℝ) (i : Fin 4) (p : Four) : ℂ :=
  (sectionWeight κ τ i p.1 p.2.1 p.2.2.1 p.2.2.2:ℂ)

theorem actual_contDiff (κ τ : ℝ) (i : Fin 4) : ContDiff ℝ ∞ (actual κ τ i) := by
  have h : ContDiff ℝ ∞ (fun p : Four => sectionWeight κ τ i p.1 p.2.1 p.2.2.1 p.2.2.2) :=
    section_comp_contDiff κ τ i contDiff_fst (contDiff_fst.comp contDiff_snd)
      (contDiff_fst.comp (contDiff_snd.comp contDiff_snd))
      (contDiff_snd.comp (contDiff_snd.comp contDiff_snd))
  exact Complex.ofRealCLM.contDiff.comp h

theorem actual_outside {κ τ : ℝ} {i : Fin 4} (hτ : 0<τ) {p : Four}
    (hp : p∉fullBox τ) : actual κ τ i p=0 := by
  by_contra hn
  have hw : sectionWeight κ τ i p.1 p.2.1 p.2.2.1 p.2.2.2≠0 := by
    intro he
    exact hn (by simp [actual,he])
  obtain ⟨_,hX,hZ,hT,hV⟩ := section_nonzero_box κ τ i p.1 p.2.1 p.2.2.1 p.2.2.2 hτ hw
  exact hp ⟨mem_symmetric.mpr hX,mem_symmetric.mpr hZ,mem_symmetric.mpr hT,mem_symmetric.mpr hV.le⟩

private def step (e : Four) (f : Four→ℂ) : Four→ℂ := fun p => fderiv ℝ f p e
private def iterateStep (e : Four) : ℕ→(Four→ℂ)→(Four→ℂ)
  | 0,f => f
  | n+1,f => step e (iterateStep e n f)

private theorem step_smooth (e : Four) {f : Four→ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (step e f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private theorem iterateStep_smooth (e : Four) {f : Four→ℂ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) : ContDiff ℝ ∞ (iterateStep e n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact step_smooth e ih

private theorem iterateStep_germ (e : Four) {f : Four→ℂ} {p : Four}
    (h : f=ᶠ[𝓝 p] (fun _ => 0)) (n : ℕ) :
    iterateStep e n f=ᶠ[𝓝 p] (fun _ => 0) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    have h' := (ih.fderiv (𝕜:=ℝ)).fun_comp (fun L : Four→L[ℝ]ℂ => L e)
    simpa [iterateStep,step] using h'

private theorem iterateStep_outside {κ τ : ℝ} {i : Fin 4} (hτ : 0<τ)
    (e : Four) (n : ℕ) {p : Four} (hp : p∉fullBox τ) :
    iterateStep e n (actual κ τ i) p=0 := by
  have hg : actual κ τ i=ᶠ[𝓝 p] (fun _ => 0) := by
    have h := (fullBox_compact τ).isClosed.isOpen_compl.mem_nhds hp
    filter_upwards [h] with p' hp'
    exact actual_outside hτ hp'
  exact (iterateStep_germ e hg n).eq_of_nhds

private theorem point_deriv (axis : Axis) (X : ℝ) (p : Outer) (s : ℝ) :
    HasDerivAt (point axis X p) (dir axis) s := by
  cases axis
  · exact (hasDerivAt_const s X).prodMk ((hasDerivAt_id s).prodMk
      ((hasDerivAt_const s p.2).prodMk (hasDerivAt_const s p.1)))
  · exact (hasDerivAt_const s X).prodMk ((hasDerivAt_const s p.2).prodMk
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s p.1)))
  · exact (hasDerivAt_const s X).prodMk ((hasDerivAt_const s p.2).prodMk
      ((hasDerivAt_const s p.1).prodMk (hasDerivAt_id s)))

private theorem point_smooth (axis : Axis) (X : ℝ) (p : Outer) :
    ContDiff ℝ ∞ (point axis X p) := by
  cases axis
  · exact contDiff_const.prodMk (contDiff_id.prodMk (contDiff_const.prodMk contDiff_const))
  · exact contDiff_const.prodMk (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  · exact contDiff_const.prodMk (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

@[expose] def row (κ τ X : ℝ) (i : Fin 4) (axis : Axis) (p : Outer) : ℝ→ℂ :=
  fun s => actual κ τ i (point axis X p s)

theorem row_smooth (κ τ X : ℝ) (i : Fin 4) (axis : Axis) (p : Outer) :
    ContDiff ℝ ∞ (row κ τ X i axis p) :=
  (actual_contDiff κ τ i).comp (point_smooth axis X p)

private theorem row_iter_eq (κ τ X : ℝ) (i : Fin 4) (axis : Axis) (p : Outer) (n : ℕ) :
    iteratedDeriv n (row κ τ X i axis p) =
      fun s => iterateStep (dir axis) n (actual κ τ i) (point axis X p s) := by
  induction n with
  | zero => simp only [iteratedDeriv_zero] <;> rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    have h := (iterateStep_smooth (dir axis) (actual_contDiff κ τ i) n).differentiable (by simp)
    funext s
    exact ((h _).hasFDerivAt.comp_hasDerivAt s (point_deriv axis X p s)).deriv

theorem row_deriv_zero_outside (κ τ X : ℝ) (i : Fin 4) (axis : Axis) (p : Outer)
    (s : ℝ) (n : ℕ) (hτ : 0<τ) (h : rowR axis τ<|s|) :
    iteratedDeriv n (row κ τ X i axis p) s=0 := by
  rw [row_iter_eq]
  apply iterateStep_outside hτ
  intro hp
  exact (not_le_of_lt h) ((point_in_box axis τ X p s).mp hp).2.2

theorem row_zero_outside_outer (κ τ X : ℝ) (i : Fin 4) (axis : Axis) (p : Outer)
    (hτ : 0<τ) (hp : p∉outerBox axis τ) : row κ τ X i axis p=0 := by
  funext s
  apply actual_outside hτ
  intro h
  exact hp ((point_in_box axis τ X p s).mp h).2.1

theorem row_deriv_integrable (κ τ X : ℝ) (i : Fin 4) (axis : Axis) (p : Outer)
    (n : ℕ) (hτ : 0<τ) : Integrable (iteratedDeriv n (row κ τ X i axis p)) := by
  have hc : Continuous (iteratedDeriv n (row κ τ X i axis p)) := by
    rw [row_iter_eq]
    exact (iterateStep_smooth _ (actual_contDiff κ τ i) n).continuous.comp
      (point_smooth _ _ _).continuous
  have hK : IsCompact (symmetric (rowR axis τ)) := isCompact_Icc
  have hs : Function.support (iteratedDeriv n (row κ τ X i axis p)) ⊆ symmetric (rowR axis τ) := by
    intro s hs
    by_contra hn
    exact hs (row_deriv_zero_outside κ τ X i axis p s n hτ (lt_of_not_ge (fun h => hn (mem_symmetric.mpr h))))
  exact hc.integrable_of_hasCompactSupport
    (hK.of_isClosed_subset isClosed_closure (closure_minimal hs hK.isClosed))

/-- For each pure axis and each order the actual chart supplies a uniform
bound on all real X and all real row inputs. No mixed derivative input. -/
theorem pure_uniform (κ τ : ℝ) (i : Fin 4) (axis : Axis) (n : ℕ) (hτ : 0<τ) :
    ∃ J : ℝ, 1≤J ∧ ∀ X p s, ‖iteratedDeriv n (row κ τ X i axis p) s‖≤J := by
  let f := iterateStep (dir axis) n (actual κ τ i)
  have hn : (fullBox τ).Nonempty := ⟨(0,0,0,0),by
    simp only [fullBox,Set.mem_prod,mem_symmetric,abs_zero]
    exact ⟨by norm_num,by norm_num,by norm_num,by positivity⟩⟩
  have hc : Continuous (fun p => ‖f p‖) :=
    (iterateStep_smooth _ (actual_contDiff κ τ i) n).continuous.norm
  obtain ⟨y,_,hm⟩ := (fullBox_compact τ).exists_isMaxOn hn hc.continuousOn
  let J := max 1 ‖f y‖
  have hJ : 1≤J := le_max_left _ _
  refine ⟨J,hJ,?_⟩
  intro X p s
  rw [row_iter_eq]
  change ‖f (point axis X p s)‖≤J
  by_cases hp : point axis X p s∈fullBox τ
  · exact (hm hp).trans (le_max_right _ _)
  · rw [show f (point axis X p s)=0 from iterateStep_outside hτ _ _ hp,norm_zero]
    linarith

theorem radius_nonneg (axis : Axis) (τ : ℝ) (hτ : 0<τ) :
    0≤rowR axis τ ∧ 0≤outerR₁ axis τ := by
  cases axis <;> norm_num [rowR,outerR₁] <;> positivity

/-- Closed interval exact length; includes the physical thin row 4τ. -/
theorem interval_L1 (f : ℝ→ℂ) (hf : Integrable f) (R C : ℝ) (hR : 0≤R)
    (hC : ∀ s,‖f s‖≤C) (hz : ∀ s, R<|s|→f s=0) :
    (∫ s,‖f s‖)≤(2*R)*C := by
  let K := symmetric R
  have hm : MeasurableSet K := measurableSet_Icc
  have hfin : volume K ≠ ⊤ := isCompact_Icc.measure_ne_top
  calc
    _ = ∫ s in K,‖f s‖ := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro s hs
      rw [hz s (lt_of_not_ge (fun h => hs (mem_symmetric.mpr h))),norm_zero]
    _ ≤ ∫ _ in K,C :=
      setIntegral_mono_on hf.norm.integrableOn (integrableOn_const hfin) hm (fun s _ => hC s)
    _ = _ := by
      rw [setIntegral_const,smul_eq_mul]
      change volume.real (Set.Icc (-R) R)*C=_
      rw [Real.volume_real_Icc_of_le (by linarith : -R≤R)]
      ring

theorem row_L1 (κ τ X : ℝ) (i : Fin 4) (axis : Axis) (p : Outer) (n : ℕ)
    (hτ : 0<τ) (J : ℝ) (hJ : ∀ s, ‖iteratedDeriv n (row κ τ X i axis p) s‖≤J) :
    (∫ s,‖iteratedDeriv n (row κ τ X i axis p) s‖)≤(2*rowR axis τ)*J :=
  interval_L1 _ (row_deriv_integrable κ τ X i axis p n hτ) _ _ (radius_nonneg axis τ hτ).1
    hJ (fun s h => row_deriv_zero_outside κ τ X i axis p s n hτ h)

end ActualPureChartAxes318
