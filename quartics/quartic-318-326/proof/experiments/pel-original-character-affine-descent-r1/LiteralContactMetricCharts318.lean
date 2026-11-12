module
public import FourRootSpecifiedFiniteCharts318
public import SourceMetricCharts318
public section
noncomputable section
namespace LiteralContactMetricCharts318
open Set Filter FourRootNormalizedPointCharts318 LiteralMetricExtension318 SourceMetricCharts318
open scoped Topology Manifold ContDiff
local instance : TopologicalSpace (Completed contacts) := FourRootGluedTopology318.topology contacts
local instance : ChartedSpace ℂ (Completed contacts) := FourRootCompletedComplexAtlas318.chartedSpace contacts contacts_injective
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Completed contacts) := FourRootCompletedComplexAtlas318.complex_manifold contacts contacts_injective

@[expose] def base : Completed contacts → ℂ
  | .inl q => q.val.1
  | .inr _ => 0
@[expose] def Regular : Completed contacts → Prop
  | .inl q => ∀ i,q.val.1≠contacts i
  | .inr _ => False
@[expose] def coordinate : Chart → ℂ → ℂ
  | .regular t _ => fun z => t+z
  | .finiteBranch i => fun z => contacts i+z^2
  | .infinity => fun z => 1/z^2

/-- Actual selected maximal charts realizing the three literal metric
coordinate types. The punctured germ supplies every nearby regular
point with its SAME original t coordinate, not an abstract disk model. -/
structure Data (p : Completed contacts) where
  kind : Chart
  chart : OpenPartialHomeomorph (Completed contacts) ℂ
  mem : p∈chart.source
  maximal : chart∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (Completed contacts)
  regular_kind : Regular p → ∃ h : ∀ i,base p≠contacts i,kind=.regular (base p) h
  regular_axis : Regular p → ∀ q : FinitePoints contacts,chart (.inl q)=q.val.1
  punctured : ∀ᶠ z in 𝓝 (0 : ℂ),z≠0 →
    Regular (chart.symm (chart p+z)) ∧ base (chart.symm (chart p+z))=coordinate kind z

lemma roots_ne (p : FinitePoints contacts) (hp : ∀ i,p.val.1≠contacts i) (i : Fin 4) :
    p.val.2 i≠0 := by
  intro hz
  have hh := p.property i
  rw [hz,zero_pow (by decide : 2≠0)] at hh
  exact hp i (sub_eq_zero.mp hh.symm)
lemma regular_of_roots_ne (p : FinitePoints contacts) (hp : ∀ i,p.val.2 i≠0) :
    Regular (.inl p) := by
  intro i hi
  have hh := p.property i
  rw [hi,sub_self] at hh
  exact hp i (pow_eq_zero hh)

@[expose] def regularData (p : FinitePoints contacts) (hp : ∀ i,p.val.1≠contacts i) : Data (.inl p) := by
  obtain ⟨e,he,ha,hi⟩ := FourRootSpecifiedFiniteCharts318.exists_regular contacts p (roots_ne p hp)
  let E := e.lift_openEmbedding (FourRootGluedTopology318.finite_openEmbedding contacts)
  have hEp : E (.inl p)=p.val.1 :=
    (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).trans (ha p)
  refine ⟨.regular p.val.1 hp,E,⟨p,he,rfl⟩,
    FourRootSpecifiedFiniteCharts318.lifted_maximal contacts contacts_injective e hi,
    fun _ => ⟨hp,rfl⟩,?_,?_⟩
  · intro _ q
    exact (OpenPartialHomeomorph.lift_openEmbedding_apply _ _).trans (ha q)
  · have hn : ∀ᶠ z in 𝓝 (0 : ℂ),p.val.1+z∈e.target :=
      (continuousAt_const.add continuousAt_id).eventually
        (by simpa only [add_zero,←ha p] using e.open_target.mem_nhds (e.map_source he))
    have hh : ∀ᶠ z in 𝓝 (0 : ℂ),∀ i,p.val.1+z≠contacts i := by
      apply Filter.eventually_all.mpr
      intro i
      exact (continuousAt_const.add continuousAt_id).eventually
        (by simpa only [add_zero] using eventually_ne_nhds (hp i))
    filter_upwards [hn,hh] with z hz ht
    intro _
    have hv : (e.symm (p.val.1+z)).val.1=p.val.1+z := by
      rw [←ha,e.right_inv hz]
    change Regular (.inl (e.symm (E (.inl p)+z))) ∧
      (e.symm (E (.inl p)+z)).val.1=p.val.1+z
    rw [hEp]
    exact ⟨by intro i;rw [hv];exact ht i,hv⟩

@[expose] def branchData (p : FinitePoints contacts) (i : Fin 4) (hp : p.val.1=contacts i) :
    Data (.inl p) := by
  obtain ⟨e,he,ha,hi⟩ := FourRootSpecifiedFiniteCharts318.exists_branch contacts contacts_injective p i hp
  let E := e.lift_openEmbedding (FourRootGluedTopology318.finite_openEmbedding contacts)
  have hEp : E (.inl p)=0 := by
    rw [show E (.inl p)=e p from OpenPartialHomeomorph.lift_openEmbedding_apply _ _,ha]
    exact FourRootFiniteBranchGraph318.root_zero contacts i p hp
  have hep : e p=0 := by
    rw [ha]
    exact FourRootFiniteBranchGraph318.root_zero contacts i p hp
  have hnot : ¬Regular (.inl p) := fun h => h i hp
  refine ⟨.finiteBranch i,E,⟨p,he,rfl⟩,
    FourRootSpecifiedFiniteCharts318.lifted_maximal contacts contacts_injective e hi,
    fun h => (hnot h).elim,fun h => (hnot h).elim,?_⟩
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ),z∈e.target := by
    simpa only [hep] using e.open_target.mem_nhds (e.map_source he)
  have hh : ∀ᶠ z in 𝓝 (0 : ℂ),∀ j,j≠i → contacts i+z^2≠contacts j := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hj : j=i
    · exact Filter.Eventually.of_forall (fun _ hn => (hn hj).elim)
    · have hne : contacts i≠contacts j := contacts_injective.ne hj.symm
      exact ((continuousAt_const.add (continuousAt_id.pow 2)).eventually
        (by simpa only [zero_pow (by decide : 2≠0),add_zero] using eventually_ne_nhds hne)).mono
          (fun z hz _ => hz)
  filter_upwards [hn,hh] with z hz ht
  intro hzne
  have hr : (e.symm z).val.2 i=z := by rw [←ha,e.right_inv hz]
  have hv : (e.symm z).val.1=contacts i+z^2 := by
    have hh := (e.symm z).property i
    rw [hr] at hh
    linear_combination -hh
  change Regular (.inl (e.symm (E (.inl p)+z))) ∧
    (e.symm (E (.inl p)+z)).val.1=contacts i+z^2
  rw [hEp,zero_add]
  refine ⟨?_,hv⟩
  intro j
  rw [hv]
  by_cases hj : j=i
  · subst j
    intro heq
    have hz2 : z^2=0 := by linear_combination heq
    exact hzne (pow_eq_zero hz2)
  · exact ht j hj

@[expose] def infinityData (s : InfinitySigns) : Data (.inr s) := by
  let e := FourRootInfinityComplexCharts318.chart contacts s
  let E := FourRootCompletedComplexAtlas318.infinityChart contacts s
  let p := FourRootInfinityGraph318.center contacts s
  have he : p∈e.source := FourRootInfinityComplexCharts318.chart_center contacts s
  have hep : e p=0 := FourRootInfinityComplexCharts318.chart_axis contacts s p
  have hEp : E (.inr s)=0 := by
    rw [←infinityChart_zero contacts s]
    exact (FourRootCompletedComplexAtlas318.infinity_apply contacts s p).trans hep
  refine ⟨.infinity,E,⟨p,he,infinityChart_zero contacts s⟩,
    IsManifold.subset_maximalAtlas ⟨Sum.inr s,rfl⟩,
    fun h => h.elim,fun h => h.elim,?_⟩
  have hn : ∀ᶠ z in 𝓝 (0 : ℂ),z∈e.target := by
    simpa only [hep] using e.open_target.mem_nhds (e.map_source he)
  have hi : e.symm 0=p := by rw [←hep];exact e.left_inv he
  have hc : ContinuousAt (fun z => (e.symm z).val.2) 0 := by
    have hE : ContinuousAt e.symm 0 := e.continuousAt_symm (by simpa only [hep] using e.map_source he)
    exact continuous_snd.continuousAt.comp (continuous_subtype_val.continuousAt.comp hE)
  have hh : ∀ᶠ z in 𝓝 (0 : ℂ),∀ i,(e.symm z).val.2 i≠0 := by
    apply Filter.eventually_all.mpr
    intro i
    have hs : s.val i≠0 := by
      intro hz
      have h := s.property.2 i
      rw [hz] at h
      norm_num at h
    have hs0 : (e.symm 0).val.2 i≠0 := by simpa only [hi] using hs
    exact ((continuous_apply i).continuousAt.comp hc).eventually (eventually_ne_nhds hs0)
  filter_upwards [hn,hh] with z hz ht
  intro hzne
  have hu : (e.symm z).val.1=z := by
    rw [←FourRootInfinityComplexCharts318.chart_axis contacts s,e.right_inv hz]
  have hun : (e.symm z).val.1≠0 := by rwa [hu]
  let q := (toFinite contacts ⟨e.symm z,hun⟩).val
  have hq : Regular (.inl q) := regular_of_roots_ne q (fun i => div_ne_zero (ht i) hun)
  have hv : q.val.1=1/z^2 := by
    change contacts 0+((e.symm z).val.1^2)⁻¹=1/z^2
    rw [hu]
    simp only [contacts,Matrix.cons_val_zero,zero_add,one_div]
  change Regular (infinityChart contacts (e.symm (E (.inr s)+z))) ∧
    base (infinityChart contacts (e.symm (E (.inr s)+z)))=1/z^2
  rw [hEp,zero_add,infinityChart_nonzero contacts _ hun]
  exact ⟨hq,hv⟩

/-- The actual completed carrier supplies every chosen metric chart,
including all finite ramification and all eight infinity sign points. -/
@[expose] def data (p : Completed contacts) : Data p := by
  cases p with
  | inl q =>
    by_cases hq : ∀ i,q.val.1≠contacts i
    · exact regularData q hq
    · push_neg at hq
      obtain ⟨i,hi⟩ := hq
      exact branchData q i hi
  | inr s => exact infinityData s
end LiteralContactMetricCharts318
