module
public import QuaternionicRealPeriod318
public import Mathlib.Geometry.Manifold.Instances.Quotient
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Algebra.Module.ZLattice.Basic
public section
noncomputable section
namespace DiscreteComplexPeriodAtlas318
open QuaternionicRealPeriod318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1200000
variable (L : AddSubgroup ComplexVectors) [DiscreteTopology L]
abbrev Quotient := ComplexVectors ⧸ L
@[expose] def projection : ComplexVectors → Quotient L := QuotientAddGroup.mk

theorem quotient_covering : IsAddQuotientCoveringMap (projection L) L :=
  L.isAddQuotientCoveringMap_of_comm (isDiscrete_iff_discreteTopology.mpr inferInstance)

theorem quotient_localHomeomorph : IsLocalHomeomorph (projection L) :=
  (quotient_covering L).isLocalHomeomorph

theorem quotient_surjective : Function.Surjective (projection L) :=
  QuotientAddGroup.mk'_surjective L

theorem quotient_hausdorff : T2Space (Quotient L) := by
  letI : IsClosed (L : Set ComplexVectors) := AddSubgroup.isClosed_of_discreteTopology
  infer_instance

@[expose] def localChart (a : ComplexVectors) : OpenPartialHomeomorph (Quotient L) ComplexVectors :=
  (quotient_localHomeomorph L).localInverseAt a

theorem localChart_symm (a z : ComplexVectors) : (localChart L a).symm z=projection L z := by
  rw [localChart,(quotient_localHomeomorph L).localInverseAt_symm]

theorem localChart_center (a : ComplexVectors) : projection L a∈(localChart L a).source :=
  (quotient_localHomeomorph L).apply_self_mem_localInverseAt_source

/-- Actual inverse charts differ locally by a TRANSLATION in the same
period quotient; holomorphy is derived, not assumed for local inverses. -/
theorem local_inverse_translation (b w : ComplexVectors)
    (hw : projection L w∈(localChart L b).source) :
    ∃ d : ComplexVectors, projection L d=0 ∧
      (fun z => localChart L b (projection L z))=ᶠ[𝓝 w] (fun z => z+d) := by
  let d := localChart L b (projection L w)-w
  have hv : projection L (localChart L b (projection L w))=projection L w := by
    have h := (localChart L b).left_inv hw
    rw [localChart_symm] at h
    exact h
  have hd : projection L d=0 := by
    change (QuotientAddGroup.mk' L) (localChart L b (projection L w)-w)=0
    rw [map_sub,hv,sub_self]
  have hshift (z : ComplexVectors) : projection L (z+d)=projection L z := by
    change (QuotientAddGroup.mk' L)(z+d)=(QuotientAddGroup.mk' L)z
    rw [map_add,show (QuotientAddGroup.mk' L)d=0 from hd,add_zero]
  have hc : ContinuousAt (fun z : ComplexVectors => z+d) w :=
    continuousAt_id.add continuousAt_const
  have hw' : w+d∈(localChart L b).target := by
    have hh : w+d=localChart L b (projection L w) := by dsimp [d]; abel
    rw [hh]
    exact (localChart L b).map_source hw
  refine ⟨d,hd,?_⟩
  filter_upwards [hc.eventually ((localChart L b).open_target.mem_nhds hw')] with z hz
  have h := (localChart L b).right_inv hz
  rw [localChart_symm,hshift] at h
  exact h

theorem analytic_local_inverse (b w : ComplexVectors)
    (hw : projection L w∈(localChart L b).source) :
    AnalyticAt ℂ (fun z => localChart L b (projection L z)) w := by
  obtain ⟨d,hd,he⟩ := local_inverse_translation L b w hw
  have ha : AnalyticAt ℂ (fun z : ComplexVectors => z+d) w :=
    analyticAt_id.add analyticAt_const
  exact ha.congr he.symm

theorem analytic_transition (a b : ComplexVectors) :
    AnalyticOnNhd ℂ ((localChart L a).symm.trans (localChart L b))
      ((localChart L a).symm.trans (localChart L b)).source := by
  intro w hw
  have hh : projection L w∈(localChart L b).source := by
    simpa only [localChart_symm] using hw.2
  simpa only [OpenPartialHomeomorph.coe_trans,Function.comp_apply,localChart_symm] using
    analytic_local_inverse L b w hh

@[expose, instance_reducible] def chartedSpace : ChartedSpace ComplexVectors (Quotient L) where
  atlas := Set.range (localChart L)
  chartAt q := localChart L ((quotient_surjective L q).choose)
  mem_chart_source q := Set.mem_of_eq_of_mem (quotient_surjective L q).choose_spec.symm
    (localChart_center L ((quotient_surjective L q).choose))
  chart_mem_atlas q := ⟨_,rfl⟩

/-- A genuine complex two-dimensional manifold on the existing additive
quotient, with its existing quotient topology and actual covering charts. -/
theorem complex_manifold :
    letI := chartedSpace L
    IsManifold 𝓘(ℂ,ComplexVectors) ω (Quotient L) := by
  letI := chartedSpace L
  apply isManifold_of_contDiffOn
  rintro e e' ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition L a b).contDiffOn
      ((localChart L a).symm.trans (localChart L b)).open_source.uniqueDiffOn
end DiscreteComplexPeriodAtlas318
