module
public import LegendrePlaneOverlapHolomorphy318
public section
noncomputable section
namespace LegendreCompletedComplexAtlas318
open LegendrePlaneOverlap318 Set Filter
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2800000
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]
abbrev Finite := LegendreFiniteComplexAtlas318.Plane l
abbrev Infinite := InfinityPlane l

@[expose] def finiteChart (p : Finite l) : OpenPartialHomeomorph (CompletedPlane l) ℂ :=
  (LegendreFiniteComplexAtlas318.chart l p).lift_openEmbedding (finite_open l)
@[expose] def infinityChart (p : Infinite l) : OpenPartialHomeomorph (CompletedPlane l) ℂ :=
  (LegendreInfinityComplexAtlas318.chart l p).lift_openEmbedding (infinity_open l)

lemma finite_inverse (p : Finite l) (z : ℂ) :
    (finiteChart l p).symm z=LegendrePlaneOverlap318.finiteChart l
      ((LegendreFiniteComplexAtlas318.chart l p).symm z) := rfl
lemma infinity_inverse (p : Infinite l) (z : ℂ) :
    (infinityChart l p).symm z=LegendrePlaneOverlap318.infinityChart l
      ((LegendreInfinityComplexAtlas318.chart l p).symm z) := rfl
lemma finite_apply (p q : Finite l) : finiteChart l p (LegendrePlaneOverlap318.finiteChart l q)=
    LegendreFiniteComplexAtlas318.chart l p q :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _
lemma infinity_apply (p q : Infinite l) : infinityChart l p (LegendrePlaneOverlap318.infinityChart l q)=
    LegendreInfinityComplexAtlas318.chart l p q :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _

/-- Cross-chart source membership forces the ACTUAL denominator to be
nonzero, by the original exact two-chart gluing relation. -/
lemma finite_to_infinity_denominator (p : Finite l) (q : Infinite l) (z : ℂ)
    (hz : z∈((finiteChart l p).symm.trans (infinityChart l q)).source) :
    ((LegendreFiniteComplexAtlas318.chart l p).symm z).val.2≠0 := by
  obtain ⟨r,hr,he⟩ := hz.2
  have h : LegendrePlaneOverlap318.finiteChart l
      ((LegendreFiniteComplexAtlas318.chart l p).symm z)=
        LegendrePlaneOverlap318.infinityChart l r := he.symm
  exact ((chart_identification l _ _).mp h).1
lemma infinity_to_finite_denominator (p : Infinite l) (q : Finite l) (z : ℂ)
    (hz : z∈((infinityChart l p).symm.trans (finiteChart l q)).source) :
    ((LegendreInfinityComplexAtlas318.chart l p).symm z).val.2≠0 := by
  obtain ⟨r,hr,he⟩ := hz.2
  have h : LegendrePlaneOverlap318.finiteChart l r=
      LegendrePlaneOverlap318.infinityChart l
        ((LegendreInfinityComplexAtlas318.chart l p).symm z) := he
  obtain ⟨hy,heq⟩ := (chart_identification l _ _).mp h
  rw [←heq]
  exact toInfinity_nonzero l r hy

lemma finite_to_infinity_value (p : Finite l) (q : Infinite l) (z : ℂ)
    (hz : ((LegendreFiniteComplexAtlas318.chart l p).symm z).val.2≠0) :
    infinityChart l q ((finiteChart l p).symm z)=
      LegendreInfinityComplexAtlas318.chart l q
        (toInfinity l ((LegendreFiniteComplexAtlas318.chart l p).symm z)) := by
  rw [finite_inverse]
  rw [(chart_identification l
    ((LegendreFiniteComplexAtlas318.chart l p).symm z)
    (toInfinity l ((LegendreFiniteComplexAtlas318.chart l p).symm z))).mpr ⟨hz,rfl⟩]
  exact infinity_apply l q _
lemma infinity_to_finite_value (p : Infinite l) (q : Finite l) (z : ℂ)
    (hz : ((LegendreInfinityComplexAtlas318.chart l p).symm z).val.2≠0) :
    finiteChart l q ((infinityChart l p).symm z)=
      LegendreFiniteComplexAtlas318.chart l q
        (toFinite l ((LegendreInfinityComplexAtlas318.chart l p).symm z)) := by
  rw [infinity_inverse]
  have he := (chart_identification l
    (toFinite l ((LegendreInfinityComplexAtlas318.chart l p).symm z))
    ((LegendreInfinityComplexAtlas318.chart l p).symm z)).mpr
      ⟨toFinite_nonzero l _ hz,right_inverse l _ hz⟩
  rw [←he]
  exact finite_apply l q _

/-- The genuine mixed transitions are the original rational coordinate
formulas, analytic throughout their full actual overlap sources. -/
theorem finite_to_infinity_analytic (p : Finite l) (q : Infinite l) :
    AnalyticOnNhd ℂ ((finiteChart l p).symm.trans (infinityChart l q))
      ((finiteChart l p).symm.trans (infinityChart l q)).source := by
  intro z hz
  have ha := LegendreFiniteComplexAtlas318.inverse_analytic l p z hz.1
  have hd := finite_to_infinity_denominator l p q z hz
  have hn := (analyticAt_snd.comp ha).continuousAt.eventually (eventually_ne_nhds hd)
  rcases LegendreInfinityComplexAtlas318.chart_axis l q with haxis | haxis
  · have hh := (analyticAt_fst.comp ha).div (analyticAt_snd.comp ha) hd
    apply hh.congr
    filter_upwards [hn] with w hw
    change _=infinityChart l q ((finiteChart l p).symm w)
    rw [finite_to_infinity_value l p q w hw,haxis,toInfinity_value l _ hw]
  · have hh : AnalyticAt ℂ
        (fun w => 1/((LegendreFiniteComplexAtlas318.chart l p).symm w).val.2) z :=
      analyticAt_const.div (analyticAt_snd.comp ha) hd
    apply hh.congr
    filter_upwards [hn] with w hw
    change _=infinityChart l q ((finiteChart l p).symm w)
    rw [finite_to_infinity_value l p q w hw,haxis,toInfinity_value l _ hw]

theorem infinity_to_finite_analytic (p : Infinite l) (q : Finite l) :
    AnalyticOnNhd ℂ ((infinityChart l p).symm.trans (finiteChart l q))
      ((infinityChart l p).symm.trans (finiteChart l q)).source := by
  intro z hz
  have ha := LegendreInfinityComplexAtlas318.inverse_analytic l p z hz.1
  have hd := infinity_to_finite_denominator l p q z hz
  have hn := (analyticAt_snd.comp ha).continuousAt.eventually (eventually_ne_nhds hd)
  rcases LegendreFiniteComplexAtlas318.chart_axis l q with haxis | haxis
  · have hh := (analyticAt_fst.comp ha).div (analyticAt_snd.comp ha) hd
    apply hh.congr
    filter_upwards [hn] with w hw
    change _=finiteChart l q ((infinityChart l p).symm w)
    rw [infinity_to_finite_value l p q w hw,haxis,toFinite_value l _ hw]
  · have hh : AnalyticAt ℂ
        (fun w => 1/((LegendreInfinityComplexAtlas318.chart l p).symm w).val.2) z :=
      analyticAt_const.div (analyticAt_snd.comp ha) hd
    apply hh.congr
    filter_upwards [hn] with w hw
    change _=finiteChart l q ((infinityChart l p).symm w)
    rw [infinity_to_finite_value l p q w hw,haxis,toFinite_value l _ hw]

@[expose] def localChart : Finite l ⊕ Infinite l → OpenPartialHomeomorph (CompletedPlane l) ℂ :=
  Sum.elim (finiteChart l) (infinityChart l)
lemma covers (p : CompletedPlane l) : ∃i,p∈(localChart l i).source := by
  rcases chart_cover l p with ⟨q,rfl⟩ | ⟨q,rfl⟩
  · exact ⟨Sum.inl q,⟨q,LegendreFiniteComplexAtlas318.chart_center l q,rfl⟩⟩
  · exact ⟨Sum.inr q,⟨q,LegendreInfinityComplexAtlas318.chart_center l q,rfl⟩⟩

theorem analytic_transition (i j : Finite l ⊕ Infinite l) :
    AnalyticOnNhd ℂ ((localChart l i).symm.trans (localChart l j))
      ((localChart l i).symm.trans (localChart l j)).source := by
  cases i with
  | inl p =>
    cases j with
    | inl q =>
      simpa only [localChart,Sum.elim_inl,finiteChart,OpenPartialHomeomorph.lift_openEmbedding_trans]
        using LegendreFiniteComplexAtlas318.analytic_transition l p q
    | inr q => exact finite_to_infinity_analytic l p q
  | inr p =>
    cases j with
    | inl q => exact infinity_to_finite_analytic l p q
    | inr q =>
      simpa only [localChart,Sum.elim_inr,infinityChart,OpenPartialHomeomorph.lift_openEmbedding_trans]
        using LegendreInfinityComplexAtlas318.analytic_transition l p q

@[expose,instance_reducible] def chartedSpace : ChartedSpace ℂ (CompletedPlane l) where
  atlas := Set.range (localChart l)
  chartAt p := localChart l (covers l p).choose
  mem_chart_source p := (covers l p).choose_spec
  chart_mem_atlas p := ⟨(covers l p).choose,rfl⟩

/-- A GLOBAL complex atlas on the independently glued actual polynomial
charts, including infinity. No source torus topology or atlas is transported. -/
theorem complex_manifold : letI:=chartedSpace l; IsManifold 𝓘(ℂ,ℂ) ω (CompletedPlane l) := by
  letI:=chartedSpace l
  apply isManifold_of_contDiffOn
  rintro e e' ⟨i,rfl⟩ ⟨j,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition l i j).contDiffOn
      ((localChart l i).symm.trans (localChart l j)).open_source.uniqueDiffOn
end LegendreCompletedComplexAtlas318
