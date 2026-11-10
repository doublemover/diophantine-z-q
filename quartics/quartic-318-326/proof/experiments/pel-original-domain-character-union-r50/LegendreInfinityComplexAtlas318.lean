module
public import LegendreInfinityIndependentGraphs318
public import AnalyticZeroLocusChart318
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public section
noncomputable section
namespace LegendreInfinityComplexAtlas318
open LegendreIndependentGraphs318 AnalyticZeroLocusChart318
open Set Filter
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2400000
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]

/-- Actual infinity-chart complex points in the INDEPENDENT ambient plane topology. -/
abbrev Plane := ZeroLocus (infinityEquation l)

@[expose] def swap (f : ℂ × ℂ → ℂ) :
    ZeroLocus f ≃ₜ ZeroLocus (fun v => f (v.2,v.1)) where
  toFun q := ⟨(q.val.2,q.val.1),q.property⟩
  invFun q := ⟨(q.val.2,q.val.1),q.property⟩
  left_inv q := by apply Subtype.ext; exact Prod.ext rfl rfl
  right_inv q := by apply Subtype.ext; exact Prod.ext rfl rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Independent implicit graphs produce actual infinity charts, using x
OR y at vertical tangencies. No source uniformization is used. -/
theorem exists_infinity_chart (p : Plane l) :
    ∃ e : OpenPartialHomeomorph (Plane l) ℂ,p∈e.source ∧
      ((∀q,e q=q.val.1) ∨ (∀q,e q=q.val.2)) ∧
      AnalyticOnNhd ℂ (fun x => (e.symm x).val) e.target := by
  rcases LegendreInfinityIndependentGraphs318.graph l p.val p.property with ⟨g,hg,hg0,he,hu⟩ | ⟨g,hg,hg0,he,hu⟩
  · obtain ⟨e,hp,haxis,ha⟩ := exists_chart (infinityEquation l) p g hg hg0 he hu
    exact ⟨e,hp,Or.inl haxis,ha⟩
  · have ht : Tendsto (fun v : ℂ × ℂ => (v.2,v.1))
        (𝓝 (p.val.2,p.val.1)) (𝓝 p.val) := by
      exact (by fun_prop : ContinuousAt (fun v : ℂ × ℂ => (v.2,v.1)) (p.val.2,p.val.1)).tendsto
    have hu' : ∀ᶠ v in 𝓝 (p.val.2,p.val.1),infinityEquation l (v.2,v.1)=0 ↔ g v.1=v.2 :=
      ht.eventually hu
    obtain ⟨e,hp,haxis,ha⟩ := exists_chart (fun v => infinityEquation l (v.2,v.1))
      (swap (infinityEquation l) p) g hg hg0 he hu'
    let E := (swap (infinityEquation l)).toOpenPartialHomeomorph.trans e
    refine ⟨E,⟨Set.mem_univ p,hp⟩,Or.inr ?_,?_⟩
    · intro q
      exact haxis (swap (infinityEquation l) q)
    · intro x hx
      change AnalyticAt ℂ (fun z => ((e.symm z).val.2,(e.symm z).val.1)) x
      exact (analyticAt_snd.comp (ha x hx.1)).prod (analyticAt_fst.comp (ha x hx.1))

@[expose] def chart (p : Plane l) : OpenPartialHomeomorph (Plane l) ℂ :=
  (exists_infinity_chart l p).choose
lemma chart_center (p : Plane l) : p∈(chart l p).source := (exists_infinity_chart l p).choose_spec.1
lemma chart_axis (p : Plane l) :
    (∀q,chart l p q=q.val.1) ∨ (∀q,chart l p q=q.val.2) :=
  (exists_infinity_chart l p).choose_spec.2.1
lemma inverse_analytic (p : Plane l) :
    AnalyticOnNhd ℂ (fun z => ((chart l p).symm z).val) (chart l p).target :=
  (exists_infinity_chart l p).choose_spec.2.2

/-- Transitions are actual coordinate projections of independent
holomorphic inverse graphs, including x-to-y and y-to-x overlaps. -/
theorem analytic_transition (p q : Plane l) :
    AnalyticOnNhd ℂ ((chart l p).symm.trans (chart l q))
      ((chart l p).symm.trans (chart l q)).source := by
  intro z hz
  have ha := inverse_analytic l p z hz.1
  rcases chart_axis l q with hx | hy
  · have he : (fun w => chart l q ((chart l p).symm w))=
        (fun w => ((chart l p).symm w).val.1) := funext (fun w => hx _)
    change AnalyticAt ℂ (fun w => chart l q ((chart l p).symm w)) z
    rw [he]
    exact analyticAt_fst.comp ha
  · have he : (fun w => chart l q ((chart l p).symm w))=
        (fun w => ((chart l p).symm w).val.2) := funext (fun w => hy _)
    change AnalyticAt ℂ (fun w => chart l q ((chart l p).symm w)) z
    rw [he]
    exact analyticAt_snd.comp ha

@[expose,instance_reducible] def chartedSpace : ChartedSpace ℂ (Plane l) where
  atlas := Set.range (chart l)
  chartAt := chart l
  mem_chart_source := chart_center l
  chart_mem_atlas p := ⟨p,rfl⟩

/-- The actual infinity polynomial zero locus is now an independently
constructed complex curve, not a structure transported from the source cover. -/
theorem complex_manifold : letI:=chartedSpace l; IsManifold 𝓘(ℂ,ℂ) ω (Plane l) := by
  letI:=chartedSpace l
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p,rfl⟩ ⟨q,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition l p q).contDiffOn
      ((chart l p).symm.trans (chart l q)).open_source.uniqueDiffOn
/-- Ambient coordinates are genuinely holomorphic for this independent
atlas; its analytic meaning is not supplied by the later source bijection. -/
theorem coordinates_analytic : letI:=chartedSpace l;
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) ω (fun p : Plane l => p.val) := by
  letI:=chartedSpace l
  intro p
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt,?_⟩
  change ContDiffWithinAt ℂ ω (fun z => ((chart l p).symm z).val) _ (chart l p p)
  exact (inverse_analytic l p (chart l p p)
    ((chart l p).map_source (chart_center l p))).contDiffAt.contDiffWithinAt
end LegendreInfinityComplexAtlas318
