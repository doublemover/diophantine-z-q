module
public import OriginalPeriodPlaneOverlapHolomorphy318
public section
noncomputable section
namespace OriginalPeriodCompletedComplexAtlas318
open OriginalPeriodPlaneOverlap318 ComplexAffineFreeTranslation318 Set Filter
open scoped Topology Manifold ContDiff
set_option maxHeartbeats 2800000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]
abbrev Finite := OriginalPeriodFiniteComplexAtlas318.Plane L
abbrev Infinite := InfinityPlane L

@[expose] def finiteChart (p : Finite L) : OpenPartialHomeomorph (CompletedPlane L) ℂ :=
  (OriginalPeriodFiniteComplexAtlas318.chart L p).lift_openEmbedding (finite_open L)
@[expose] def infinityChart (p : Infinite L) : OpenPartialHomeomorph (CompletedPlane L) ℂ :=
  (OriginalPeriodInfinityComplexAtlas318.chart L p).lift_openEmbedding (infinity_open L)

lemma finite_inverse (p : Finite L) (z : ℂ) :
    (finiteChart L p).symm z=OriginalPeriodPlaneOverlap318.finiteChart L
      ((OriginalPeriodFiniteComplexAtlas318.chart L p).symm z) := rfl
lemma infinity_inverse (p : Infinite L) (z : ℂ) :
    (infinityChart L p).symm z=OriginalPeriodPlaneOverlap318.infinityChart L
      ((OriginalPeriodInfinityComplexAtlas318.chart L p).symm z) := rfl
lemma finite_apply (p q : Finite L) : finiteChart L p (OriginalPeriodPlaneOverlap318.finiteChart L q)=
    OriginalPeriodFiniteComplexAtlas318.chart L p q :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _
lemma infinity_apply (p q : Infinite L) : infinityChart L p (OriginalPeriodPlaneOverlap318.infinityChart L q)=
    OriginalPeriodInfinityComplexAtlas318.chart L p q :=
  OpenPartialHomeomorph.lift_openEmbedding_apply _ _

/-- Cross-chart source membership forces the ACTUAL denominator to be
nonzero, by the original exact two-chart gluing relation. -/
lemma finite_to_infinity_denominator (p : Finite L) (q : Infinite L) (z : ℂ)
    (hz : z∈((finiteChart L p).symm.trans (infinityChart L q)).source) :
    ((OriginalPeriodFiniteComplexAtlas318.chart L p).symm z).val.2≠0 := by
  obtain ⟨r,hr,he⟩ := hz.2
  have h : OriginalPeriodPlaneOverlap318.finiteChart L
      ((OriginalPeriodFiniteComplexAtlas318.chart L p).symm z)=
        OriginalPeriodPlaneOverlap318.infinityChart L r := he.symm
  exact ((chart_identification L _ _).mp h).1
lemma infinity_to_finite_denominator (p : Infinite L) (q : Finite L) (z : ℂ)
    (hz : z∈((infinityChart L p).symm.trans (finiteChart L q)).source) :
    ((OriginalPeriodInfinityComplexAtlas318.chart L p).symm z).val.2≠0 := by
  obtain ⟨r,hr,he⟩ := hz.2
  have h : OriginalPeriodPlaneOverlap318.finiteChart L r=
      OriginalPeriodPlaneOverlap318.infinityChart L
        ((OriginalPeriodInfinityComplexAtlas318.chart L p).symm z) := he
  obtain ⟨hy,heq⟩ := (chart_identification L _ _).mp h
  rw [←heq]
  exact toInfinity_nonzero L r hy

lemma finite_to_infinity_value (p : Finite L) (q : Infinite L) (z : ℂ)
    (hz : ((OriginalPeriodFiniteComplexAtlas318.chart L p).symm z).val.2≠0) :
    infinityChart L q ((finiteChart L p).symm z)=
      OriginalPeriodInfinityComplexAtlas318.chart L q
        (toInfinity L ((OriginalPeriodFiniteComplexAtlas318.chart L p).symm z)) := by
  rw [finite_inverse]
  rw [(chart_identification L
    ((OriginalPeriodFiniteComplexAtlas318.chart L p).symm z)
    (toInfinity L ((OriginalPeriodFiniteComplexAtlas318.chart L p).symm z))).mpr ⟨hz,rfl⟩]
  exact infinity_apply L q _
lemma infinity_to_finite_value (p : Infinite L) (q : Finite L) (z : ℂ)
    (hz : ((OriginalPeriodInfinityComplexAtlas318.chart L p).symm z).val.2≠0) :
    finiteChart L q ((infinityChart L p).symm z)=
      OriginalPeriodFiniteComplexAtlas318.chart L q
        (toFinite L ((OriginalPeriodInfinityComplexAtlas318.chart L p).symm z)) := by
  rw [infinity_inverse]
  have he := (chart_identification L
    (toFinite L ((OriginalPeriodInfinityComplexAtlas318.chart L p).symm z))
    ((OriginalPeriodInfinityComplexAtlas318.chart L p).symm z)).mpr
      ⟨toFinite_nonzero L _ hz,right_inverse L _ hz⟩
  rw [←he]
  exact finite_apply L q _

/-- The genuine mixed transitions are the original rational coordinate
formulas, analytic throughout their full actual overlap sources. -/
theorem finite_to_infinity_analytic (p : Finite L) (q : Infinite L) :
    AnalyticOnNhd ℂ ((finiteChart L p).symm.trans (infinityChart L q))
      ((finiteChart L p).symm.trans (infinityChart L q)).source := by
  intro z hz
  have ha := OriginalPeriodFiniteComplexAtlas318.inverse_analytic L p z hz.1
  have hd := finite_to_infinity_denominator L p q z hz
  have hn := (analyticAt_snd.comp ha).continuousAt.eventually (eventually_ne_nhds hd)
  rcases OriginalPeriodInfinityComplexAtlas318.chart_axis L q with haxis | haxis
  · have hh := (analyticAt_fst.comp ha).div (analyticAt_snd.comp ha) hd
    apply hh.congr
    filter_upwards [hn] with w hw
    change _=infinityChart L q ((finiteChart L p).symm w)
    rw [finite_to_infinity_value L p q w hw,haxis,toInfinity_value L _ hw]
  · have hh : AnalyticAt ℂ
        (fun w => 1/((OriginalPeriodFiniteComplexAtlas318.chart L p).symm w).val.2) z :=
      analyticAt_const.div (analyticAt_snd.comp ha) hd
    apply hh.congr
    filter_upwards [hn] with w hw
    change _=infinityChart L q ((finiteChart L p).symm w)
    rw [finite_to_infinity_value L p q w hw,haxis,toInfinity_value L _ hw]

theorem infinity_to_finite_analytic (p : Infinite L) (q : Finite L) :
    AnalyticOnNhd ℂ ((infinityChart L p).symm.trans (finiteChart L q))
      ((infinityChart L p).symm.trans (finiteChart L q)).source := by
  intro z hz
  have ha := OriginalPeriodInfinityComplexAtlas318.inverse_analytic L p z hz.1
  have hd := infinity_to_finite_denominator L p q z hz
  have hn := (analyticAt_snd.comp ha).continuousAt.eventually (eventually_ne_nhds hd)
  rcases OriginalPeriodFiniteComplexAtlas318.chart_axis L q with haxis | haxis
  · have hh := (analyticAt_fst.comp ha).div (analyticAt_snd.comp ha) hd
    apply hh.congr
    filter_upwards [hn] with w hw
    change _=finiteChart L q ((infinityChart L p).symm w)
    rw [infinity_to_finite_value L p q w hw,haxis,toFinite_value L _ hw]
  · have hh : AnalyticAt ℂ
        (fun w => 1/((OriginalPeriodInfinityComplexAtlas318.chart L p).symm w).val.2) z :=
      analyticAt_const.div (analyticAt_snd.comp ha) hd
    apply hh.congr
    filter_upwards [hn] with w hw
    change _=finiteChart L q ((infinityChart L p).symm w)
    rw [infinity_to_finite_value L p q w hw,haxis,toFinite_value L _ hw]

@[expose] def localChart : Finite L ⊕ Infinite L → OpenPartialHomeomorph (CompletedPlane L) ℂ :=
  Sum.elim (finiteChart L) (infinityChart L)
lemma covers (p : CompletedPlane L) : ∃i,p∈(localChart L i).source := by
  rcases chart_cover L p with ⟨q,rfl⟩ | ⟨q,rfl⟩
  · exact ⟨Sum.inl q,⟨q,OriginalPeriodFiniteComplexAtlas318.chart_center L q,rfl⟩⟩
  · exact ⟨Sum.inr q,⟨q,OriginalPeriodInfinityComplexAtlas318.chart_center L q,rfl⟩⟩

theorem analytic_transition (i j : Finite L ⊕ Infinite L) :
    AnalyticOnNhd ℂ ((localChart L i).symm.trans (localChart L j))
      ((localChart L i).symm.trans (localChart L j)).source := by
  cases i with
  | inl p =>
    cases j with
    | inl q =>
      simpa only [localChart,Sum.elim_inl,finiteChart,OpenPartialHomeomorph.lift_openEmbedding_trans]
        using OriginalPeriodFiniteComplexAtlas318.analytic_transition L p q
    | inr q => exact finite_to_infinity_analytic L p q
  | inr p =>
    cases j with
    | inl q => exact infinity_to_finite_analytic L p q
    | inr q =>
      simpa only [localChart,Sum.elim_inr,infinityChart,OpenPartialHomeomorph.lift_openEmbedding_trans]
        using OriginalPeriodInfinityComplexAtlas318.analytic_transition L p q

@[expose,instance_reducible] def chartedSpace : ChartedSpace ℂ (CompletedPlane L) where
  atlas := Set.range (localChart L)
  chartAt p := localChart L (covers L p).choose
  mem_chart_source p := (covers L p).choose_spec
  chart_mem_atlas p := ⟨(covers L p).choose,rfl⟩

/-- A GLOBAL complex atlas on the independently glued actual polynomial
charts, including infinity. No source torus topology or atlas is transported. -/
theorem complex_manifold : letI:=chartedSpace L; IsManifold 𝓘(ℂ,ℂ) ω (CompletedPlane L) := by
  letI:=chartedSpace L
  apply isManifold_of_contDiffOn
  rintro e e' ⟨i,rfl⟩ ⟨j,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (analytic_transition L i j).contDiffOn
      ((localChart L i).symm.trans (localChart L j)).open_source.uniqueDiffOn
end OriginalPeriodCompletedComplexAtlas318
