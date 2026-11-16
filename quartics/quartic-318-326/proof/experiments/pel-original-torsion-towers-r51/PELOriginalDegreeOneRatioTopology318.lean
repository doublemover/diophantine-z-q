module
public import PELOriginalDegreeOneRatioBundle318
public section
noncomputable section
namespace PELOriginalDegreeOneRatioTopology318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 Filter Topology
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalDegreeOneRatioBundle318
variable (τ:ℂ)(hτ:0<τ.im)
@[expose] def mapTotal(p:PELOriginalPolarizationLineBundle318.Total τ hτ):MixedTotal τ hτ:=
  ⟨p.1,fiberEquivalence τ hτ p.1 p.2⟩
@[expose] def inverseTotal(p:MixedTotal τ hτ):PELOriginalPolarizationLineBundle318.Total τ hτ:=
  ⟨p.1,(fiberEquivalence τ hτ p.1).symm p.2⟩
lemma left_inverse:Function.LeftInverse (inverseTotal τ hτ) (mapTotal τ hτ):=by
  rintro ⟨q,v⟩
  change (⟨q,(fiberEquivalence τ hτ q).symm (fiberEquivalence τ hτ q v)⟩:
    PELOriginalPolarizationLineBundle318.Total τ hτ)=⟨q,v⟩
  rw [LinearEquiv.symm_apply_apply]
lemma right_inverse:Function.RightInverse (inverseTotal τ hτ) (mapTotal τ hτ):=by
  rintro ⟨q,v⟩
  change (⟨q,fiberEquivalence τ hτ q ((fiberEquivalence τ hτ q).symm v)⟩:
    MixedTotal τ hτ)=⟨q,v⟩
  rw [LinearEquiv.apply_symm_apply]
@[expose] def sectionCoefficient(a:ComplexVectors)(j:Index)(q:Base τ):ℂ:=
  PELOriginalHyperplanePullbackTopology318.sectionCoefficient τ hτ 1 a j.1 q /
    PELOriginalHyperplanePullbackTopology318.sectionCoefficient τ hτ 0 a j.2 q
lemma coefficient_continuousAt(a:ComplexVectors)(j:Index)(q:Base τ)
    (ha:q∈baseSet τ hτ a)(hj:q∈domain τ hτ j):ContinuousAt (sectionCoefficient τ hτ a j) q:=
  (PELOriginalHyperplanePullbackTopology318.coefficient_continuousAt τ hτ 1 a j.1 q ha).div
    (PELOriginalHyperplanePullbackTopology318.coefficient_continuousAt τ hτ 0 a j.2 q ha)
    (PELOriginalHyperplanePullbackTopology318.coefficient_ne τ hτ 0 a j.2 q hj.2)
lemma coefficient_ne(a:ComplexVectors)(j:Index)(q:Base τ)
    (hj:q∈domain τ hτ j):sectionCoefficient τ hτ a j q≠0:=
  div_ne_zero (PELOriginalHyperplanePullbackTopology318.coefficient_ne τ hτ 1 a j.1 q hj.1)
    (PELOriginalHyperplanePullbackTopology318.coefficient_ne τ hτ 0 a j.2 q hj.2)

lemma map_continuous:Continuous (mapTotal τ hτ):=by
  apply continuous_iff_continuousAt.mpr
  intro p
  let a:ComplexVectors:=(core τ hτ).indexAt p.1
  let j:Index:=(mixedCore τ hτ).indexAt p.1
  have ha:p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hj:p.1∈(mixedCore τ hτ).baseSet j:=(mixedCore τ hτ).mem_baseSet_at _
  have hp:ContinuousAt (fun r:PELOriginalPolarizationLineBundle318.Total τ hτ=>r.1) p:=
    (PELOriginalPolarizationLineBundle318.core τ hτ).continuous_proj.continuousAt
  apply ((mixedCore τ hτ).localTriv j).continuousAt_of_comp_left hp hj
  have hnum:=(((PELOriginalPolarizationLineBundle318.core τ hτ).localTriv a).continuousAt ha).snd
  have hden:ContinuousAt (fun r:PELOriginalPolarizationLineBundle318.Total τ hτ=>sectionCoefficient τ hτ a j r.1) p:=
    (coefficient_continuousAt τ hτ a j p.1 ha hj).comp hp
  have hc:=hp.prodMk (hnum.div hden (coefficient_ne τ hτ a j p.1 hj))
  apply hc.congr_of_eventuallyEq
  filter_upwards [hp ((chart τ hτ a).open_source.mem_nhds ha),
    hp (((mixedCore τ hτ).isOpen_baseSet j).mem_nhds hj)] with r hra hrj
  apply Prod.ext
  · rfl
  · exact (original_chart_ratio τ hτ a r.1 hra j hrj r.2).symm

lemma inverse_coordinate(a:ComplexVectors)(j:Index)(p:MixedTotal τ hτ)
    (ha:p.1∈baseSet τ hτ a)(hj:p.1∈(mixedCore τ hτ).baseSet j):
    ((PELOriginalPolarizationLineBundle318.core τ hτ).localTriv a (inverseTotal τ hτ p)).2=
      sectionCoefficient τ hτ a j p.1*((mixedCore τ hτ).localTriv j p).2:=by
  have h:=original_chart_ratio τ hτ a p.1 ha j hj ((fiberEquivalence τ hτ p.1).symm p.2)
  rw [LinearEquiv.apply_symm_apply] at h
  have he:((mixedCore τ hτ).localTriv j p).2*
      sectionCoefficient τ hτ a j p.1=
      ((PELOriginalPolarizationLineBundle318.core τ hτ).localTriv a (inverseTotal τ hτ p)).2:=
    (eq_div_iff (coefficient_ne τ hτ a j p.1 hj)).mp h
  exact he.symm.trans (mul_comm _ _)
lemma inverse_continuous:Continuous (inverseTotal τ hτ):=by
  apply continuous_iff_continuousAt.mpr
  intro p
  let a:ComplexVectors:=(core τ hτ).indexAt p.1
  let j:Index:=(mixedCore τ hτ).indexAt p.1
  have ha:p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hj:p.1∈(mixedCore τ hτ).baseSet j:=(mixedCore τ hτ).mem_baseSet_at _
  have hp:ContinuousAt (fun r:MixedTotal τ hτ=>r.1) p:=
    (mixedCore τ hτ).continuous_proj.continuousAt
  apply ((PELOriginalPolarizationLineBundle318.core τ hτ).localTriv a).continuousAt_of_comp_left hp ha
  have hnum:=(((mixedCore τ hτ).localTriv j).continuousAt hj).snd
  have hden:ContinuousAt (fun r:MixedTotal τ hτ=>sectionCoefficient τ hτ a j r.1) p:=
    (coefficient_continuousAt τ hτ a j p.1 ha hj).comp hp
  apply (hp.prodMk (hden.mul hnum)).congr_of_eventuallyEq
  filter_upwards [hp ((chart τ hτ a).open_source.mem_nhds ha),
    hp (((mixedCore τ hτ).isOpen_baseSet j).mem_nhds hj)] with r hra hrj
  apply Prod.ext
  · rfl
  · exact (inverse_coordinate τ hτ a j r hra hrj).symm

/-- Actual total-space homeomorphism from the ORIGINAL degree-one line,
fiberwise complex-linear and over the identity of the original base.
Both independently constructed bundle topologies remain unchanged. -/
@[expose] def homeomorph:PELOriginalPolarizationLineBundle318.Total τ hτ≃ₜMixedTotal τ hτ where
  toFun:=mapTotal τ hτ
  invFun:=inverseTotal τ hτ
  left_inv:=left_inverse τ hτ
  right_inv:=right_inverse τ hτ
  continuous_toFun:=map_continuous τ hτ
  continuous_invFun:=inverse_continuous τ hτ
lemma over_base(p:PELOriginalPolarizationLineBundle318.Total τ hτ):(homeomorph τ hτ p).1=p.1:=rfl
end PELOriginalDegreeOneRatioTopology318
