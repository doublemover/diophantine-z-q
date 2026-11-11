module
public import RiemannNormalizedUniqueness318
public import Mathlib.Analysis.Calculus.Deriv.Star
public section
noncomputable section
namespace ReflectedConformalChart318
open Set Metric Filter Topology
open scoped ComplexConjugate
set_option maxHeartbeats 2600000
@[expose] def J (z : ℂ) : ℂ := -conj z
lemma J_J (z : ℂ) : J (J z)=z := by simp [J]
lemma J_continuous : Continuous J := (show Continuous (conj : ℂ → ℂ) from continuous_star).neg
lemma J_norm (z : ℂ) : ‖J z‖=‖z‖ := by simp [J]
lemma J_disk (z : ℂ) : J z∈ball (0:ℂ) 1 ↔ z∈ball 0 1 := by
  simp only [Metric.mem_ball,dist_zero_right,J_norm]
@[expose] def reflected (f : ℂ → ℂ) : ℂ → ℂ := fun z => J (f (J z))

/-- The two anti-holomorphic reflections give a genuine complex derivative,
with both minus signs cancelling. -/
theorem reflected_derivative {f : ℂ → ℂ} {z d : ℂ} (hf : HasDerivAt f d (J z)) :
    HasDerivAt (reflected f) (conj d) z := by
  have hn := hf.comp (conj z) (hasDerivAt_id (conj z)).neg
  have hc := hn.conj_conj.neg
  simpa [reflected,J,Function.comp_def] using hc

section Chart
variable {U : Set ℂ} (hU : IsOpen U) (hJ : ∀ z, J z∈U ↔ z∈U)
    (e : OpenPartialHomeomorph ℂ ℂ) (hs : e.source=U) (ht : e.target=ball 0 1)

@[expose] def chart : OpenPartialHomeomorph ℂ ℂ where
  toFun := reflected e
  invFun := reflected e.symm
  source := U
  target := ball 0 1
  map_source' := by
    intro z hz
    apply (J_disk _).mpr
    exact ht ▸ e.map_source (hs.symm ▸ (hJ z).mpr hz)
  map_target' := by
    intro w hw
    apply (hJ _).mpr
    exact hs ▸ e.map_target (ht.symm ▸ (J_disk w).mpr hw)
  left_inv' := by
    intro z hz
    simp only [reflected,J_J]
    rw [e.left_inv (hs.symm ▸ (hJ z).mpr hz),J_J]
  right_inv' := by
    intro w hw
    simp only [reflected,J_J]
    rw [e.right_inv (ht.symm ▸ (J_disk w).mpr hw),J_J]
  open_source := hU
  open_target := isOpen_ball
  continuousOn_toFun := by
    apply J_continuous.comp_continuousOn
    apply e.continuousOn.comp J_continuous.continuousOn
    intro z hz
    exact hs.symm ▸ (hJ z).mpr hz
  continuousOn_invFun := by
    apply J_continuous.comp_continuousOn
    apply e.symm.continuousOn.comp J_continuous.continuousOn
    intro w hw
    exact ht.symm ▸ (J_disk w).mpr hw

theorem chart_source : (chart hU hJ e hs ht).source=U := rfl
theorem chart_target : (chart hU hJ e hs ht).target=ball 0 1 := rfl

theorem chart_analytic (ha : ∀ z∈U,AnalyticAt ℂ e z) :
    ∀ z∈U,AnalyticAt ℂ (chart hU hJ e hs ht) z := by
  have hd : DifferentiableOn ℂ (reflected e) U := by
    intro z hz
    exact (reflected_derivative ((ha (J z) ((hJ z).mpr hz)).differentiableAt.hasDerivAt)).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd hU

theorem chart_inverse_analytic (hi : ∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w) :
    ∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ (chart hU hJ e hs ht).symm w := by
  have hd : DifferentiableOn ℂ (reflected e.symm) (ball 0 1) := by
    intro w hw
    exact (reflected_derivative ((hi (J w) ((J_disk w).mpr hw)).differentiableAt.hasDerivAt)).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd isOpen_ball
end Chart

/-- Uniqueness forces the actual normalized conformal map to intertwine
source and target anti-holomorphic mirrors. No boundary values are used. -/
theorem normalized_mirror {U : Set ℂ} (hU : IsOpen U) (hJ : ∀ z, J z∈U ↔ z∈U)
    (e : OpenPartialHomeomorph ℂ ℂ) (hs : e.source=U) (ht : e.target=ball 0 1)
    (ha : ∀ z∈U,AnalyticAt ℂ e z) (hi : ∀ w∈ball (0:ℂ) 1,AnalyticAt ℂ e.symm w)
    {z₀ : ℂ} (hz : z₀∈U) (hfixed : J z₀=z₀) (hzero : e z₀=0)
    (him : (deriv e z₀).im=0) (hre : 0<(deriv e z₀).re) :
    ∀ z∈U,e (J z)=J (e z) := by
  let g := chart hU hJ e hs ht
  have hg0 : g z₀=0 := by change J (e (J z₀))=0; simp [hfixed,hzero,J]
  have hd : deriv g z₀=conj (deriv e z₀) := by
    have hh : HasDerivAt e (deriv e z₀) (J z₀) := hfixed.symm ▸ (ha z₀ hz).differentiableAt.hasDerivAt
    exact (reflected_derivative hh).deriv
  have hgi : (deriv g z₀).im=0 := by rw [hd]; simp [him]
  have hgr : 0<(deriv g z₀).re := by rw [hd]; simpa using hre
  have heq := RiemannNormalizedUniqueness318.normalized_unique e g hs rfl ht rfl ha
    (chart_analytic hU hJ e hs ht ha) hi (chart_inverse_analytic hU hJ e hs ht hi)
    hz hzero hg0 him hgi hre hgr
  intro z hzu
  have hh := congrArg J (heq hzu)
  change J (e z)=J (J (e (J z))) at hh
  rw [J_J] at hh
  exact hh.symm
end ReflectedConformalChart318
