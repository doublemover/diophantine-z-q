module
public import OriginalPeriodIndependentGraphComparison318
public import AnalyticZeroLocusChart318
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public section
noncomputable section
namespace OriginalPeriodFiniteComplexAtlas318
open OriginalPeriodIndependentGraphs318 AnalyticZeroLocusChart318
open ComplexAffineFreeTranslation318 Set Filter
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Actual finite complex points in the INDEPENDENT ambient plane topology. -/
abbrev Plane := ZeroLocus (finiteEquation L)

@[expose] def swap (f : ℂ × ℂ → ℂ) :
    ZeroLocus f ≃ₜ ZeroLocus (fun v => f (v.2,v.1)) where
  toFun q := ⟨(q.val.2,q.val.1),q.property⟩
  invFun q := ⟨(q.val.2,q.val.1),q.property⟩
  left_inv q := by apply Subtype.ext; exact Prod.ext rfl rfl
  right_inv q := by apply Subtype.ext; exact Prod.ext rfl rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Independent implicit graphs produce actual finite charts, using x
OR y at vertical tangencies. No source period uniformization is used. -/
theorem exists_finite_chart (p : Plane L) :
    ∃ e : OpenPartialHomeomorph (Plane L) ℂ,p∈e.source ∧
      ((∀q,e q=q.val.1) ∨ (∀q,e q=q.val.2)) ∧
      AnalyticOnNhd ℂ (fun x => (e.symm x).val) e.target := by
  rcases finite_graph L p.val p.property with ⟨g,hg,hg0,he,hu⟩ | ⟨g,hg,hg0,he,hu⟩
  · obtain ⟨e,hp,haxis,ha⟩ := exists_chart (finiteEquation L) p g hg hg0 he hu
    exact ⟨e,hp,Or.inl haxis,ha⟩
  · have ht : Tendsto (fun v : ℂ × ℂ => (v.2,v.1))
        (𝓝 (p.val.2,p.val.1)) (𝓝 p.val) := by
      exact (by fun_prop : ContinuousAt (fun v : ℂ × ℂ => (v.2,v.1)) (p.val.2,p.val.1)).tendsto
    have hu' : ∀ᶠ v in 𝓝 (p.val.2,p.val.1),finiteEquation L (v.2,v.1)=0 ↔ g v.1=v.2 :=
      ht.eventually hu
    obtain ⟨e,hp,haxis,ha⟩ := exists_chart (fun v => finiteEquation L (v.2,v.1))
      (swap (finiteEquation L) p) g hg hg0 he hu'
    let E := (swap (finiteEquation L)).toOpenPartialHomeomorph.trans e
    refine ⟨E,⟨Set.mem_univ p,hp⟩,Or.inr ?_,?_⟩
    · intro q
      exact haxis (swap (finiteEquation L) q)
    · intro x hx
      change AnalyticAt ℂ (fun z => ((e.symm z).val.2,(e.symm z).val.1)) x
      exact (analyticAt_snd.comp (ha x hx.1)).prod (analyticAt_fst.comp (ha x hx.1))

@[expose] def chart (p : Plane L) : OpenPartialHomeomorph (Plane L) ℂ :=
  (exists_finite_chart L p).choose
lemma chart_center (p : Plane L) : p∈(chart L p).source := (exists_finite_chart L p).choose_spec.1
lemma chart_axis (p : Plane L) :
    (∀q,chart L p q=q.val.1) ∨ (∀q,chart L p q=q.val.2) :=
  (exists_finite_chart L p).choose_spec.2.1
lemma inverse_analytic (p : Plane L) :
    AnalyticOnNhd ℂ (fun z => ((chart L p).symm z).val) (chart L p).target :=
  (exists_finite_chart L p).choose_spec.2.2

/-- Transitions are actual coordinate projections of independent
holomorphic inverse graphs, including x-to-y and y-to-x overlaps. -/
theorem analytic_transition (p q : Plane L) :
    AnalyticOnNhd ℂ ((chart L p).symm.trans (chart L q))
      ((chart L p).symm.trans (chart L q)).source := by
  intro z hz
  have ha := inverse_analytic L p z hz.1
  rcases chart_axis L q with hx | hy
  · have he : (fun w => chart L q ((chart L p).symm w))=
        (fun w => ((chart L p).symm w).val.1) := funext (fun w => hx _)
    change AnalyticAt ℂ (fun w => chart L q ((chart L p).symm w)) z
    rw [he]
    exact analyticAt_fst.comp ha
  · have he : (fun w => chart L q ((chart L p).symm w))=
        (fun w => ((chart L p).symm w).val.2) := funext (fun w => hy _)
    change AnalyticAt ℂ (fun w => chart L q ((chart L p).symm w)) z
    rw [he]
    exact analyticAt_snd.comp ha

@[expose,instance_reducible] def chartedSpace : ChartedSpace ℂ (Plane L) where
  atlas := Set.range (chart L)
  chartAt := chart L
  mem_chart_source := chart_center L
  chart_mem_atlas p := ⟨p,rfl⟩

/-- The actual finite polynomial zero locus is now an independently
constructed complex curve, not a structure transported from the torus. -/
theorem complex_manifold : letI:=chartedSpace L; IsManifold 𝓘(ℂ,ℂ) ω (Plane L) := by
  letI:=chartedSpace L
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p,rfl⟩ ⟨q,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition L p q).contDiffOn
      ((chart L p).symm.trans (chart L q)).open_source.uniqueDiffOn
/-- Ambient coordinates are genuinely holomorphic for this independent
atlas; its analytic meaning is not supplied by the later torus bijection. -/
theorem coordinates_analytic : letI:=chartedSpace L;
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ × ℂ) ω (fun p : Plane L => p.val) := by
  letI:=chartedSpace L
  intro p
  apply contMDiffAt_iff.mpr
  refine ⟨continuous_subtype_val.continuousAt,?_⟩
  change ContDiffWithinAt ℂ ω (fun z => ((chart L p).symm z).val) _ (chart L p p)
  exact (inverse_analytic L p (chart L p p)
    ((chart L p).map_source (chart_center L p))).contDiffAt.contDiffWithinAt
end OriginalPeriodFiniteComplexAtlas318
