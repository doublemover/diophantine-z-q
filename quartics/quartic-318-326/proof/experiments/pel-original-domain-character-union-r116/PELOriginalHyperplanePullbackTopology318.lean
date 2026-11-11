module
public import PELOriginalHyperplanePullback318
public section
noncomputable section
namespace PELOriginalHyperplanePullbackTopology318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 Filter Topology
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalHyperplanePullback318
variable (τ:ℂ)(hτ:0<τ.im)(n:ℕ)
@[expose] def mapTotal(p:PowerTotal τ hτ (n+2)):PullbackTotal τ hτ n:=
  ⟨p.1,fiberEquivalence τ hτ n p.1 p.2⟩
@[expose] def inverseTotal(p:PullbackTotal τ hτ n):PowerTotal τ hτ (n+2):=
  ⟨p.1,(fiberEquivalence τ hτ n p.1).symm p.2⟩
lemma left_inverse:Function.LeftInverse (inverseTotal τ hτ n) (mapTotal τ hτ n):=by
  rintro ⟨q,v⟩
  change (⟨q,(fiberEquivalence τ hτ n q).symm (fiberEquivalence τ hτ n q v)⟩:
    PowerTotal τ hτ (n+2))=⟨q,v⟩
  rw [LinearEquiv.symm_apply_apply]
lemma right_inverse:Function.RightInverse (inverseTotal τ hτ n) (mapTotal τ hτ n):=by
  rintro ⟨q,v⟩
  change (⟨q,fiberEquivalence τ hτ n q ((fiberEquivalence τ hτ n q).symm v)⟩:
    PullbackTotal τ hτ n)=⟨q,v⟩
  rw [LinearEquiv.apply_symm_apply]
@[expose] def sectionCoefficient(a:ComplexVectors)(j:Label (n+2))(q:Base τ):ℂ:=
  ((powerCore τ hτ (n+2)).localTriv a (levelSection τ hτ (n+2) j q)).2
lemma coefficient_continuousAt(a:ComplexVectors)(j:Label (n+2))(q:Base τ)
    (ha:q∈baseSet τ hτ a):ContinuousAt (sectionCoefficient τ hτ n a j) q:=
  (((powerCore τ hτ (n+2)).localTriv a).continuousAt ha).snd.comp q
    (PELOriginalLevelPowerSections318.continuous τ hτ (n+2) j).continuousAt
lemma coefficient_ne(a:ComplexVectors)(j:Label (n+2))(q:Base τ)
    (hj:q∈(pullbackCore τ hτ n).baseSet j):sectionCoefficient τ hτ n a j q≠0:=by
  change transition τ hτ ((core τ hτ).indexAt q) a q^(n+2)*
    (levelSection τ hτ (n+2) j q).2≠0
  exact mul_ne_zero (pow_ne_zero _ (transition_nonzero τ hτ _ _ _))
    (coordinate_ne τ hτ n q j hj)

lemma map_continuous:Continuous (mapTotal τ hτ n):=by
  apply continuous_iff_continuousAt.mpr
  intro p
  let a:ComplexVectors:=(core τ hτ).indexAt p.1
  let j:Label (n+2):=(pullbackCore τ hτ n).indexAt p.1
  have ha:p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hj:p.1∈(pullbackCore τ hτ n).baseSet j:=(pullbackCore τ hτ n).mem_baseSet_at _
  have hp:ContinuousAt (fun r:PowerTotal τ hτ (n+2)=>r.1) p:=
    (powerCore τ hτ (n+2)).continuous_proj.continuousAt
  apply ((pullbackCore τ hτ n).localTriv j).continuousAt_of_comp_left hp hj
  have hnum:=(((powerCore τ hτ (n+2)).localTriv a).continuousAt ha).snd
  have hden:ContinuousAt (fun r:PowerTotal τ hτ (n+2)=>sectionCoefficient τ hτ n a j r.1) p:=
    (coefficient_continuousAt τ hτ n a j p.1 ha).comp p hp
  have hc:=hp.prodMk (hnum.div hden (coefficient_ne τ hτ n a j p.1 hj))
  apply hc.congr_of_eventuallyEq
  filter_upwards [hp ((chart τ hτ a).open_source.mem_nhds ha),
    hp (((pullbackCore τ hτ n).isOpen_baseSet j).mem_nhds hj)] with r hra hrj
  apply Prod.ext
  · rfl
  · exact (original_chart_ratio τ hτ n a r.1 hra j hrj r.2).symm

lemma inverse_coordinate(a:ComplexVectors)(j:Label (n+2))(p:PullbackTotal τ hτ n)
    (ha:p.1∈baseSet τ hτ a)(hj:p.1∈(pullbackCore τ hτ n).baseSet j):
    ((powerCore τ hτ (n+2)).localTriv a (inverseTotal τ hτ n p)).2=
      sectionCoefficient τ hτ n a j p.1*((pullbackCore τ hτ n).localTriv j p).2:=by
  have h:=original_chart_ratio τ hτ n a p.1 ha j hj ((fiberEquivalence τ hτ n p.1).symm p.2)
  rw [LinearEquiv.apply_symm_apply] at h
  have he:((pullbackCore τ hτ n).localTriv j p).2*
      sectionCoefficient τ hτ n a j p.1=
      ((powerCore τ hτ (n+2)).localTriv a (inverseTotal τ hτ n p)).2:=
    (eq_div_iff (coefficient_ne τ hτ n a j p.1 hj)).mp h
  exact he.symm.trans (mul_comm _ _)
lemma inverse_continuous:Continuous (inverseTotal τ hτ n):=by
  apply continuous_iff_continuousAt.mpr
  intro p
  let a:ComplexVectors:=(core τ hτ).indexAt p.1
  let j:Label (n+2):=(pullbackCore τ hτ n).indexAt p.1
  have ha:p.1∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at _
  have hj:p.1∈(pullbackCore τ hτ n).baseSet j:=(pullbackCore τ hτ n).mem_baseSet_at _
  have hp:ContinuousAt (fun r:PullbackTotal τ hτ n=>r.1) p:=
    (pullbackCore τ hτ n).continuous_proj.continuousAt
  apply ((powerCore τ hτ (n+2)).localTriv a).continuousAt_of_comp_left hp ha
  have hnum:=(((pullbackCore τ hτ n).localTriv j).continuousAt hj).snd
  have hden:ContinuousAt (fun r:PullbackTotal τ hτ n=>sectionCoefficient τ hτ n a j r.1) p:=
    (coefficient_continuousAt τ hτ n a j p.1 ha).comp p hp
  apply (hp.prodMk (hden.mul hnum)).congr_of_eventuallyEq
  filter_upwards [hp ((chart τ hτ a).open_source.mem_nhds ha),
    hp (((pullbackCore τ hτ n).isOpen_baseSet j).mem_nhds hj)] with r hra hrj
  apply Prod.ext
  · rfl
  · exact (inverse_coordinate τ hτ n a j r hra hrj).symm

/-- Actual total-space homeomorphism, fiberwise complex-linear and over
identity on the original base. Both independent core topologies remain. -/
@[expose] def homeomorph:PowerTotal τ hτ (n+2)≃ₜPullbackTotal τ hτ n where
  toFun:=mapTotal τ hτ n
  invFun:=inverseTotal τ hτ n
  left_inv:=left_inverse τ hτ n
  right_inv:=right_inverse τ hτ n
  continuous_toFun:=map_continuous τ hτ n
  continuous_invFun:=inverse_continuous τ hτ n
lemma over_base(p:PowerTotal τ hτ (n+2)):(homeomorph τ hτ n p).1=p.1:=rfl
end PELOriginalHyperplanePullbackTopology318
