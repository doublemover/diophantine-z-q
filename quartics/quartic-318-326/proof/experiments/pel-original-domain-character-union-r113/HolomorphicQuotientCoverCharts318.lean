module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Topology.Covering.Quotient
public section
noncomputable section
namespace HolomorphicQuotientCoverCharts318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
variable {E M Q G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [TopologicalSpace Q] [Group G] [MulAction G M] [ContinuousConstSMul G M]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ,E) ω M]
variable (q : M → Q) (hq : IsQuotientCoveringMap q G)

@[expose] def inverseChart (a : M) : OpenPartialHomeomorph Q M := hq.isLocalHomeomorph.localInverseAt a

theorem inverseChart_symm (a x : M) : (inverseChart q hq a).symm x=q x := by
  rw [inverseChart,hq.isLocalHomeomorph.localInverseAt_symm]

/-- Genuine inverse branches of the original covering differ locally by
one FIXED original group element; it is not an assumed analytic branch. -/
theorem inverseChart_action (b w : M) (hw : q w∈(inverseChart q hq b).source) :
    ∃ g : G,inverseChart q hq b (q w)=g • w ∧
      (fun x => inverseChart q hq b (q x))=ᶠ[𝓝 w] (fun x => g • x) := by
  have hv : q (inverseChart q hq b (q w))=q w := by
    have h := (inverseChart q hq b).left_inv hw
    rw [inverseChart_symm] at h
    exact h
  obtain ⟨g,hg⟩ := hq.apply_eq_iff_mem_orbit.mp hv
  have hcenter : g • w∈(inverseChart q hq b).target := by
    rw [hg]
    exact (inverseChart q hq b).map_source hw
  have hqg (x : M) : q (g • x)=q x := hq.apply_eq_iff_mem_orbit.mpr ⟨g,rfl⟩
  refine ⟨g,hg.symm,?_⟩
  filter_upwards [(continuous_const_smul g).continuousAt.eventually
    ((inverseChart q hq b).open_target.mem_nhds hcenter)] with x hx
  have h := (inverseChart q hq b).right_inv hx
  rw [inverseChart_symm,hqg] at h
  exact h

@[expose] def quotientChart (a : M) : OpenPartialHomeomorph Q E :=
  (inverseChart q hq a).trans (chartAt E a)

theorem quotientChart_apply (a : M) (p : Q) :
    quotientChart (E:=E) q hq a p=chartAt E a (inverseChart q hq a p) := rfl

theorem quotientChart_symm (a : M) (z : E) :
    (quotientChart (E:=E) q hq a).symm z=q ((chartAt E a).symm z) := by
  change (inverseChart q hq a).symm ((chartAt E a).symm z)=_
  rw [inverseChart_symm]

theorem quotientChart_center (a : M) : q a∈(quotientChart (E:=E) q hq a).source := by
  refine ⟨hq.isLocalHomeomorph.apply_self_mem_localInverseAt_source,?_⟩
  have h : inverseChart q hq a (q a)=a := hq.isLocalHomeomorph.localInverseAt_apply_self
  rw [h]
  exact mem_chart_source E a

variable (hhol : ∀ g : G, ContMDiff 𝓘(ℂ,E) 𝓘(ℂ,E) ω (fun x : M => g • x))

include hhol in
/-- The actual covering quotient transitions are holomorphic, by composing
original maximal-atlas charts with the original holomorphic group action. -/
theorem transition_contDiffAt (a b : M) (z : E)
    (hz : z∈((quotientChart (E:=E) q hq a).symm.trans (quotientChart q hq b)).source) :
    ContDiffAt ℂ ω ((quotientChart (E:=E) q hq a).symm.trans (quotientChart q hq b)) z := by
  let p := (chartAt E a).symm z
  have ha : z∈(chartAt E a).target := hz.1.1
  have hb : q p∈(quotientChart (E:=E) q hq b).source := by
    simpa only [quotientChart_symm] using hz.2
  obtain ⟨g,hg,he⟩ := inverseChart_action q hq b p hb.1
  have hgb : g • p∈(chartAt E b).source := by rw [←hg]; exact hb.2
  have hA := contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) ha
  have hB := contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas b) hgb
  have hc : ContMDiffAt 𝓘(ℂ,E) 𝓘(ℂ,E) ω
      (fun x => chartAt E b (g • (chartAt E a).symm x)) z :=
    hB.comp z ((hhol g p).comp z hA)
  have hd : ContDiffAt ℂ ω (fun x => chartAt E b (g • (chartAt E a).symm x)) z :=
    contMDiffAt_iff_contDiffAt.mp hc
  apply hd.congr_of_eventuallyEq
  filter_upwards [((chartAt E a).symm.continuousAt ha).eventually he] with x hx
  change chartAt E b (inverseChart q hq b (q ((chartAt E a).symm x)))=_
  rw [hx]

@[expose,instance_reducible] def quotientCharts : ChartedSpace E Q where
  atlas := Set.range (quotientChart (E:=E) q hq)
  chartAt p := quotientChart q hq ((hq.surjective p).choose)
  mem_chart_source p := Set.mem_of_eq_of_mem (hq.surjective p).choose_spec.symm
    (quotientChart_center q hq ((hq.surjective p).choose))
  chart_mem_atlas p := ⟨_,rfl⟩

include hhol in
/-- Complex structure on the actual quotient topology, with no quotient
smoothness axiom and no replacement of the original group action. -/
theorem quotient_manifold :
    letI := quotientCharts (E:=E) q hq
    IsManifold 𝓘(ℂ,E) ω Q := by
  letI := quotientCharts (E:=E) q hq
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  have hc : ContDiffOn ℂ ω ((quotientChart (E:=E) q hq a).symm.trans (quotientChart q hq b))
      ((quotientChart (E:=E) q hq a).symm.trans (quotientChart q hq b)).source :=
    fun z hz => (transition_contDiffAt q hq hhol a b z hz).contDiffWithinAt
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using hc
end HolomorphicQuotientCoverCharts318
