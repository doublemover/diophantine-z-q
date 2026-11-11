module
public import PELJointPeriodDeck318
public section
noncomputable section
namespace PELJointComplexAtlas318
open QuaternionicJointPeriodTopology318 PELJointPeriodFamily318 PELJointPeriodDeck318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000
@[expose] def baseOpen : TopologicalSpace.Opens ℂ :=
  ⟨{τ | 0<τ.im},isOpen_lt continuous_const Complex.continuous_im⟩
@[expose] def baseChart : OpenPartialHomeomorph HalfPlane ℂ :=
  baseOpen.openPartialHomeomorphSubtypeCoe ⟨basePoint⟩
@[expose] def ambientChart : OpenPartialHomeomorph Cover Ambient :=
  baseChart.prod (OpenPartialHomeomorph.refl QuaternionicRealPeriod318.ComplexVectors)

theorem ambientChart_apply (p : Cover) : ambientChart p=ambient p := rfl

theorem ambientChart_source (p : Cover) : p∈ambientChart.source := by
  exact ⟨Set.mem_univ _,Set.mem_univ _⟩

theorem ambientChart_target (p : Ambient) : p∈ambientChart.target ↔ 0<p.1.im := by
  have ht : ambientChart.target = (baseOpen : Set ℂ) ×ˢ Set.univ := by
    rw [ambientChart,OpenPartialHomeomorph.prod_target,baseChart,
      TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target,
      OpenPartialHomeomorph.refl_target]
  rw [ht]
  change (0<p.1.im ∧ p.2∈(Set.univ : Set QuaternionicRealPeriod318.ComplexVectors)) ↔ _
  exact and_iff_left (Set.mem_univ _)

@[expose] def familyChart (a : Cover) : OpenPartialHomeomorph Total Ambient :=
  (inverseChart a).trans ambientChart

theorem familyChart_apply (a : Cover) (p : Total) : familyChart a p=ambient (inverseChart a p) := rfl

theorem familyChart_symm (a : Cover) (p : Ambient) :
    (familyChart a).symm p=familyProjection (ambientChart.symm p) := by
  change (inverseChart a).symm (ambientChart.symm p)=_
  rw [inverseChart_symm]

theorem familyChart_source (a : Cover) (p : Total) :
    p∈(familyChart a).source ↔ p∈(inverseChart a).source :=
  ⟨fun h => h.1,fun h => ⟨h,ambientChart_source _⟩⟩

theorem familyChart_target_upper (a : Cover) (p : Ambient) (hp : p∈(familyChart a).target) :
    p∈ambientChart.target := hp.1

theorem familyChart_center (a : Cover) : familyProjection a∈(familyChart a).source :=
  (familyChart_source a _).mpr familyProjection_localHomeomorph.apply_self_mem_localInverseAt_source

/-- Local inverse branches are jointly holomorphic because their original
order label is locally fixed, while its actual period is holomorphic in τ. -/
theorem analytic_family_inverse (b : Cover) (p : Ambient) (hp : p∈ambientChart.target)
    (hq : familyProjection (ambientChart.symm p)∈(inverseChart b).source) :
    AnalyticAt ℂ (fun z => familyChart b (familyProjection (ambientChart.symm z))) p := by
  obtain ⟨a,ha⟩ := inverseChart_deck b (ambientChart.symm p) hq
  have hc := ambientChart.symm.continuousAt hp
  have he : (fun z => familyChart b (familyProjection (ambientChart.symm z)))=ᶠ[𝓝 p]
      ambientDeck a := by
    filter_upwards [hc.eventually ha,ambientChart.open_target.mem_nhds hp] with z hz hzt
    rw [familyChart_apply,hz,deck_ambient]
    exact congrArg (ambientDeck a) (ambientChart.right_inv hzt)
  exact (ambientDeck_analytic a p).congr he.symm

theorem analytic_transition (a b : Cover) :
    AnalyticOnNhd ℂ ((familyChart a).symm.trans (familyChart b))
      ((familyChart a).symm.trans (familyChart b)).source := by
  intro p hp
  have hupper := familyChart_target_upper a p hp.1
  have hq : familyProjection (ambientChart.symm p)∈(inverseChart b).source := by
    apply (familyChart_source b _).mp
    have hs := hp.2
    change (familyChart a).symm p∈(familyChart b).source at hs
    rw [familyChart_symm] at hs
    exact hs
  change AnalyticAt ℂ (fun z => familyChart b ((familyChart a).symm z)) p
  simpa only [familyChart_symm] using analytic_family_inverse b p hupper hq

@[expose,instance_reducible] def totalCharts : ChartedSpace Ambient Total where
  atlas := Set.range familyChart
  chartAt p := familyChart ((familyProjection_surjective p).choose)
  mem_chart_source p := Set.mem_of_eq_of_mem (familyProjection_surjective p).choose_spec.symm
    (familyChart_center ((familyProjection_surjective p).choose))
  chart_mem_atlas p := ⟨_,rfl⟩

/-- A genuine complex threefold atlas on the JOINT original-period total
space, with its verified topology and actual covering charts. -/
theorem total_manifold :
    letI := totalCharts
    IsManifold 𝓘(ℂ,Ambient) ω Total := by
  letI := totalCharts
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition a b).contDiffOn
      ((familyChart a).symm.trans (familyChart b)).open_source.uniqueDiffOn
end PELJointComplexAtlas318
