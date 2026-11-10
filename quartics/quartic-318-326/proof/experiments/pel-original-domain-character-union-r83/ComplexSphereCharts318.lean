module
public import SphereInversion318
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public section
noncomputable section
namespace ComplexSphereCharts318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open SphereInversion318
set_option maxHeartbeats 2400000

/-- Standard affine chart of the EXISTING one-point compactification.
Its topology is not transported from the arithmetic source. -/
@[expose] def affine : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑):ℂ→OnePoint ℂ)).symm

lemma affine_source : affine.source=range ((↑):ℂ→OnePoint ℂ) := by simp [affine]
lemma affine_target : affine.target=univ := by simp [affine]
lemma affine_symm (z : ℂ) : affine.symm z=(z:OnePoint ℂ) := rfl
lemma affine_coe (z : ℂ) : affine (z:OnePoint ℂ)=z :=
  OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv ((↑):ℂ→OnePoint ℂ)
lemma affine_mem (z : ℂ) : (z:OnePoint ℂ)∈affine.source := by
  rw [affine_source]
  exact ⟨z,rfl⟩
lemma affine_not_infty : (∞:OnePoint ℂ)∉affine.source := by
  rw [affine_source]
  rintro ⟨z,hz⟩
  exact OnePoint.coe_ne_infty z hz

/-- Standard reciprocal chart at infinity, built from independent sphere
inversion; its overlap map with the affine chart is literally z↦1/z. -/
@[expose] def reciprocal : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  inversionHomeomorph.toOpenPartialHomeomorph.trans affine

lemma reciprocal_target : reciprocal.target=univ := by
  simp only [reciprocal,OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target,Set.preimage_univ,Set.inter_univ,affine_target]
lemma reciprocal_value (p : OnePoint ℂ) : reciprocal p=affine (inversion p) := rfl
lemma reciprocal_symm (z : ℂ) : reciprocal.symm z=inversion (z:OnePoint ℂ) := rfl
lemma reciprocal_infty : reciprocal ∞=0 := by rw [reciprocal_value,inversion_infty,affine_coe]
lemma reciprocal_mem_infty : (∞:OnePoint ℂ)∈reciprocal.source := by
  change (∞:OnePoint ℂ)∈Set.univ ∧ inversion ∞∈affine.source
  exact ⟨Set.mem_univ _,by rw [inversion_infty]; exact affine_mem 0⟩
lemma reciprocal_mem_coe {z : ℂ} (hz : z≠0) : (z:OnePoint ℂ)∈reciprocal.source := by
  change (z:OnePoint ℂ)∈Set.univ ∧ inversion (z:OnePoint ℂ)∈affine.source
  exact ⟨Set.mem_univ _,by rw [inversion_coe hz]; exact affine_mem _⟩
lemma reciprocal_coe {z : ℂ} (hz : z≠0) : reciprocal (z:OnePoint ℂ)=z⁻¹ := by
  rw [reciprocal_value,inversion_coe hz,affine_coe]
lemma reciprocal_not_zero : (0:ℂ)∉reciprocal.source := by
  intro h
  have hh : inversion (0:ℂ)∈affine.source := h.2
  rw [inversion_zero] at hh
  exact affine_not_infty hh

@[expose] def chart (b : Bool) : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  if b then reciprocal else affine

lemma self_transition (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) :
    AnalyticOnNhd ℂ (e.symm.trans e) (e.symm.trans e).source := by
  intro z hz
  apply analyticAt_id.congr
  filter_upwards [(e.symm.trans e).open_source.mem_nhds hz] with w hw
  exact (e.right_inv hw.1).symm

lemma cross_transition (b : Bool) :
    AnalyticOnNhd ℂ ((chart b).symm.trans (chart (!b)))
      ((chart b).symm.trans (chart (!b))).source := by
  intro z hz
  have hne : z≠0 := by
    intro he
    subst z
    cases b with
    | false => exact reciprocal_not_zero hz.2
    | true =>
      have hh : inversion (0:ℂ)∈affine.source := hz.2
      rw [inversion_zero] at hh
      exact affine_not_infty hh
  apply (analyticAt_id.inv hne).congr
  filter_upwards [eventually_ne_nhds hne] with w hw
  cases b with
  | false => exact (reciprocal_coe hw).symm
  | true =>
    change w⁻¹=affine (inversion (w:OnePoint ℂ))
    rw [inversion_coe hw,affine_coe]

@[expose,instance_reducible] def sphereCharts : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := range chart
  chartAt p := if p=∞ then reciprocal else affine
  mem_chart_source p := by
    split_ifs with hp
    · subst p; exact reciprocal_mem_infty
    · obtain ⟨z,rfl⟩ := OnePoint.ne_infty_iff_exists.mp hp
      exact affine_mem z
  chart_mem_atlas p := by
    by_cases hp : p=∞
    · exact ⟨true,by simp [chart,hp]⟩
    · exact ⟨false,by simp [chart,hp]⟩

/-- Genuine standard complex-sphere atlas: same charts have identity
transitions, opposite charts have the holomorphic reciprocal transition. -/
theorem sphere_manifold : letI:=sphereCharts; IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ) := by
  letI:=sphereCharts
  apply isManifold_of_contDiffOn
  rintro e f ⟨a,rfl⟩ ⟨b,rfl⟩
  have ha : AnalyticOnNhd ℂ ((chart a).symm.trans (chart b))
      ((chart a).symm.trans (chart b)).source := by
    by_cases hab : a=b
    · subst b; exact self_transition _
    · have hb : b=(!a) := by cases a <;> cases b <;> simp_all
      rw [hb]
      exact cross_transition a
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    ha.contDiffOn ((chart a).symm.trans (chart b)).open_source.uniqueDiffOn
end ComplexSphereCharts318
