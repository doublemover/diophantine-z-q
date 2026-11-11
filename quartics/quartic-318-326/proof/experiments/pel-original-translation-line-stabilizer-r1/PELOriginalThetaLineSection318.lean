module
public import PELOriginalGaugedTheta318
public section
noncomputable section
namespace PELOriginalThetaLineSection318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationAutomorphy318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318 PELOriginalPeriodLattice318
open PELOriginalAutomorphyRepresentatives318 PELOriginalDescendedMetric318
open Filter Topology
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=original_discrete τ hτ
local notation "F" => PELOriginalGaugedTheta318.value τ hτ

/-- Actual global section of the previously constructed original line.
The scalar is evaluated in its selected fiber gauge; every other genuine
chart is shown to compute the SAME original entire scalar below. -/
@[expose] def thetaSection (q:Base τ):Total τ hτ:=
  ⟨q,F (chart τ hτ ((core τ hτ).indexAt q) q)⟩
lemma projects (q:Base τ):(thetaSection τ hτ q).1=q:=rfl
lemma local_formula (a:ComplexVectors) (q:Base τ) (ha:q∈baseSet τ hτ a):
    (core τ hτ).localTriv a (thetaSection τ hτ q)=(q,F (chart τ hτ a q)):=by
  apply Prod.ext
  · rfl
  · let b:ComplexVectors:=(core τ hτ).indexAt q
    have hb:q∈baseSet τ hτ b:=(core τ hτ).mem_baseSet_at q
    have hs:chart τ hτ b q+(shift τ hτ b a q:ComplexVectors)=chart τ hτ a q:=by
      rw [shift_value τ hτ b a q hb ha];abel
    have h:=PELOriginalGaugedTheta318.original_automorphy τ hτ
      (shift τ hτ b a q) (chart τ hτ b q)
    rw [hs] at h
    exact h.symm

/-- Exact original action representative, at EVERY point of the actual
universal cover. This identifies the section of the core with the section
of the actual action quotient, including all zero values. -/
lemma original_representative (z:ComplexVectors):
    toTotal τ hτ (z,F z)=thetaSection τ hτ (projection (P τ) z):=by
  let a:ComplexVectors:=(core τ hτ).indexAt (projection (P τ) z)
  have ha:projection (P τ) z∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hs:z+(shiftTo τ hτ a z:ComplexVectors)=chart τ hτ a (projection (P τ) z):=by
    rw [shiftTo_value τ hτ a z ha];abel
  have he:=PELOriginalGaugedTheta318.original_automorphy τ hτ (shiftTo τ hτ a z) z
  rw [hs] at he
  change (⟨projection (P τ) z,factor τ hτ (shiftTo τ hτ a z) z*F z⟩:Total τ hτ)=
    ⟨projection (P τ) z,F (chart τ hτ a (projection (P τ) z))⟩
  rw [he]

lemma continuous:Continuous (thetaSection τ hτ):=by
  apply continuous_iff_continuousAt.mpr
  intro q
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at q
  apply ((core τ hτ).localTriv a).continuousAt_of_comp_left continuousAt_id ha
  have hc:ContinuousAt (fun r:Base τ=>(r,F (chart τ hτ a r))) q:=
    continuousAt_id.prodMk ((PELOriginalGaugedTheta318.holomorphic τ hτ).continuous.continuousAt.comp q
      ((chart τ hτ a).continuousAt ha))
  apply hc.congr_of_eventuallyEq
  filter_upwards [(chart τ hτ a).open_source.mem_nhds ha] with r hr
  exact (local_formula τ hτ a r hr).symm

lemma original_holomorphic_formula (a z:ComplexVectors) (hz:z∈(chart τ hτ a).target):
    ((core τ hτ).localTriv a (thetaSection τ hτ (projection (P τ) z))).2=F z:=by
  have hq:projection (P τ) z∈baseSet τ hτ a:=by
    simpa only [chart,localChart_symm] using (chart τ hτ a).map_target hz
  rw [local_formula τ hτ a _ hq]
  have he:chart τ hτ a (projection (P τ) z)=z:=by
    simpa only [chart,localChart_symm] using (chart τ hτ a).right_inv hz
  exact congrArg F he

/-- Holomorphic in EVERY actual original base chart and original line
trivialization, not merely a continuous or separately holomorphic section. -/
theorem holomorphic_in_original_charts (a:ComplexVectors):
    DifferentiableOn ℂ (fun z:ComplexVectors=>
      ((core τ hτ).localTriv a (thetaSection τ hτ (projection (P τ) z))).2)
      (chart τ hτ a).target:=by
  apply (PELOriginalGaugedTheta318.holomorphic τ hτ).differentiableOn.congr
  intro z hz
  exact original_holomorphic_formula τ hτ a z hz

lemma original_metric (z:ComplexVectors):
    metric τ hτ (thetaSection τ hτ (projection (P τ) z))=
      PELOriginalPolarizationMetric318.squaredNorm τ hτ (z,F z):=by
  rw [←original_representative τ hτ z]
  exact metric_representative τ hτ (z,F z)
end PELOriginalThetaLineSection318
