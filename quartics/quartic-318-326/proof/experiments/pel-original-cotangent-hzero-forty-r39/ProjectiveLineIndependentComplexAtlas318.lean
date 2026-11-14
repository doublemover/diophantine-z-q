module
public import ProjectiveLineIndependentPointTopology318
public import ComplexSphereCharts318
public section
noncomputable section
namespace ProjectiveLineIndependentComplexAtlas318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open ProjectiveLineComplexSchemePoints318 ProjectiveLineIndependentPointTopology318
local instance : TopologicalSpace SchemePoints:=pointTopology

/-- Actual polynomial coordinate charts on actual Scheme-valued points.
The inverse map is the ORIGINAL evaluation Spec-map, not a torus map. -/
@[expose] def pointChart (j:Fin 2) : OpenPartialHomeomorph SchemePoints ℂ:=
  ((chartPoint_open j).toOpenPartialHomeomorph (chartPoint j)).symm
lemma pointChart_source (j:Fin 2) : (pointChart j).source=range (chartPoint j):=by simp [pointChart]
lemma pointChart_target (j:Fin 2) : (pointChart j).target=univ:=by simp [pointChart]
lemma pointChart_inverse (j:Fin 2) (z:ℂ) : (pointChart j).symm z=chartPoint j z:=rfl
lemma pointChart_evaluation (j:Fin 2) (z:ℂ) : pointChart j (chartPoint j z)=z:=
  (chartPoint_open j).toOpenPartialHomeomorph_left_inv (chartPoint j)

lemma covered (p:SchemePoints) : ∃j:Fin 2,p∈(pointChart j).source := by
  obtain ⟨j,z,rfl⟩:=chartPoint_exhaustive p
  exact ⟨j,by rw [pointChart_source];exact ⟨z,rfl⟩⟩

lemma finite_to_infinity (z:ℂ) (hz:z≠0) : pointChart 0 (chartPoint 1 z)=z⁻¹:=by
  rw [reciprocal_overlap z hz,pointChart_evaluation]
lemma infinity_to_finite (z:ℂ) (hz:z≠0) : pointChart 1 (chartPoint 0 z)=z⁻¹:=by
  have he:chartPoint 1 z⁻¹=chartPoint 0 z:=by
    simpa only [inv_inv] using reciprocal_overlap z⁻¹ (inv_ne_zero hz)
  rw [←he,pointChart_evaluation]

lemma finite_overlap_nonzero (z:ℂ)
    (hz:z∈((pointChart 1).symm.trans (pointChart 0)).source) : z≠0:=by
  obtain ⟨w,hw⟩:=show chartPoint 1 z∈range (chartPoint 0) from
    (pointChart_source 0) ▸ hz.2
  exact ((chartPoint_overlap_iff z w).mp hw.symm).1
lemma infinity_overlap_nonzero (z:ℂ)
    (hz:z∈((pointChart 0).symm.trans (pointChart 1)).source) : z≠0:=by
  obtain ⟨w,hw⟩:=show chartPoint 0 z∈range (chartPoint 1) from
    (pointChart_source 1) ▸ hz.2
  obtain ⟨hw0,hwz⟩:=(chartPoint_overlap_iff w z).mp hw
  rw [hwz]
  exact inv_ne_zero hw0

/-- All mixed transition maps are the actual reciprocal coordinate on
the FULL original overlap; self transitions are genuine identities. -/
theorem analytic_transition (j k:Fin 2) :
    AnalyticOnNhd ℂ ((pointChart j).symm.trans (pointChart k))
      ((pointChart j).symm.trans (pointChart k)).source := by
  intro z hz
  by_cases hjk:j=k
  · subst k
    apply analyticAt_id.congr
    filter_upwards [((pointChart j).symm.trans (pointChart j)).open_source.mem_nhds hz] with w hw
    exact ((pointChart j).right_inv hw.1).symm
  · fin_cases j <;> fin_cases k <;> simp only [ne_eq,not_true_eq_false] at hjk
    · have hn:=infinity_overlap_nonzero z hz
      apply (analyticAt_id.inv hn).congr
      filter_upwards [eventually_ne_nhds hn] with w hw
      exact (infinity_to_finite w hw).symm
    · have hn:=finite_overlap_nonzero z hz
      apply (analyticAt_id.inv hn).congr
      filter_upwards [eventually_ne_nhds hn] with w hw
      exact (finite_to_infinity w hw).symm

@[expose,instance_reducible] def pointCharts : ChartedSpace ℂ SchemePoints where
  atlas:=range pointChart
  chartAt p:=pointChart (covered p).choose
  mem_chart_source p:=(covered p).choose_spec
  chart_mem_atlas p:=⟨(covered p).choose,rfl⟩

/-- Independent complex atlas on the actual base-preserving points of
homogeneous Proj, with its independently specified two-chart topology. -/
theorem complex_manifold : letI:=pointCharts;IsManifold 𝓘(ℂ,ℂ) ω SchemePoints := by
  letI:=pointCharts
  apply isManifold_of_contDiffOn
  rintro e e' ⟨j,rfl⟩ ⟨k,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition j k).contDiffOn
      ((pointChart j).symm.trans (pointChart k)).open_source.uniqueDiffOn
end ProjectiveLineIndependentComplexAtlas318
