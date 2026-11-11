module
public import PELOriginalHyperplanePullbackHolomorphy318
public section
noncomputable section
namespace PELOriginalDegreeOneRatioBundle318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelProjectiveMap318
open PELOriginalHyperplanePullback318
variable (τ : ℂ) (hτ : 0<τ.im)
abbrev Index := Label 3 × Label 2
local instance cubicProjectiveTopology : TopologicalSpace
    (ComplexProjectiveQuotientTopology318.Space (Label 3)) :=
  ComplexProjectiveQuotientTopology318.topology (Label 3)
local instance quadraticProjectiveTopology : TopologicalSpace
    (ComplexProjectiveQuotientTopology318.Space (Label 2)) :=
  ComplexProjectiveQuotientTopology318.topology (Label 2)

/-- Independent mixed hyperplane atlas on the ORIGINAL period surface. -/
@[expose] def domain (a : Index) : Set (Base τ) :=
  (pullbackCore τ hτ 1).baseSet a.1 ∩ (pullbackCore τ hτ 0).baseSet a.2
@[expose] def transition (a b : Index) (q : Base τ) : ℂ :=
  ComplexProjectiveHyperplaneBundle318.transition (Label 3) a.1 b.1 (projectiveMap τ hτ 1 q) /
    ComplexProjectiveHyperplaneBundle318.transition (Label 2) a.2 b.2 (projectiveMap τ hτ 0 q)

lemma transition_self (a : Index) (q : Base τ) (hq : q∈domain τ hτ a) :
    transition τ hτ a a q=1 := by
  rw [transition,ComplexProjectiveHyperplaneBundle318.transition_self _ _ _ hq.1,
    ComplexProjectiveHyperplaneBundle318.transition_self _ _ _ hq.2,div_self one_ne_zero]

lemma transition_ne (a b : Index) (q : Base τ)
    (ha : q∈domain τ hτ a) (hb : q∈domain τ hτ b) : transition τ hτ a b q≠0 :=
  div_ne_zero (ComplexProjectiveHyperplaneBundle318.transition_nonzero _ _ _ _ ha.1 hb.1)
    (ComplexProjectiveHyperplaneBundle318.transition_nonzero _ _ _ _ ha.2 hb.2)

lemma transition_comp (a b c : Index) (q : Base τ)
    (ha : q∈domain τ hτ a) (hb : q∈domain τ hτ b) (hc : q∈domain τ hτ c) :
    transition τ hτ b c q*transition τ hτ a b q=transition τ hτ a c q := by
  rw [transition,transition,transition,div_mul_div_comm,
    ComplexProjectiveHyperplaneBundle318.transition_comp _ _ _ _ _ ha.1 hb.1 hc.1,
    ComplexProjectiveHyperplaneBundle318.transition_comp _ _ _ _ _ ha.2 hb.2 hc.2]

lemma transition_continuous (a b : Index) :
    ContinuousOn (transition τ hτ a b) (domain τ hτ a ∩ domain τ hτ b) := by
  have h3 := (ComplexProjectiveHyperplaneBundle318.transition_continuous (Label 3) a.1 b.1).comp
    (PELOriginalAllLevelHolomorphicMap318.original_continuous τ hτ 1).continuousOn
    (show Set.MapsTo (projectiveMap τ hτ 1) (domain τ hτ a ∩ domain τ hτ b)
      ((ComplexProjectiveHyperplaneBundle318.core (Label 3)).baseSet a.1 ∩
        (ComplexProjectiveHyperplaneBundle318.core (Label 3)).baseSet b.1) from
      fun _ h => ⟨h.1.1,h.2.1⟩)
  have h2 := (ComplexProjectiveHyperplaneBundle318.transition_continuous (Label 2) a.2 b.2).comp
    (PELOriginalAllLevelHolomorphicMap318.original_continuous τ hτ 0).continuousOn
    (show Set.MapsTo (projectiveMap τ hτ 0) (domain τ hτ a ∩ domain τ hτ b)
      ((ComplexProjectiveHyperplaneBundle318.core (Label 2)).baseSet a.2 ∩
        (ComplexProjectiveHyperplaneBundle318.core (Label 2)).baseSet b.2) from
      fun _ h => ⟨h.1.2,h.2.2⟩)
  exact h3.div h2 (fun q h =>
    ComplexProjectiveHyperplaneBundle318.transition_nonzero _ _ _ _ h.1.2 h.2.2)

/-- The degree THREE minus degree TWO analytic bundle, built from the
independent projective hyperplane cocycles before comparison with L. -/
@[expose] def mixedCore : VectorBundleCore ℂ (Base τ) ℂ Index where
  baseSet := domain τ hτ
  isOpen_baseSet a := ((pullbackCore τ hτ 1).isOpen_baseSet a.1).inter
    ((pullbackCore τ hτ 0).isOpen_baseSet a.2)
  indexAt q := ((pullbackCore τ hτ 1).indexAt q,(pullbackCore τ hτ 0).indexAt q)
  mem_baseSet_at q := ⟨(pullbackCore τ hτ 1).mem_baseSet_at q,(pullbackCore τ hτ 0).mem_baseSet_at q⟩
  coordChange a b q := transition τ hτ a b q • ContinuousLinearMap.id ℂ ℂ
  coordChange_self a q hq v := by simp [transition_self τ hτ a q hq]
  continuousOn_coordChange a b := (transition_continuous τ hτ a b).smul continuousOn_const
  coordChange_comp a b c q hq v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [←mul_assoc,transition_comp τ hτ a b c q hq.1.1 hq.1.2 hq.2]

abbrev MixedFiber (q : Base τ) := (mixedCore τ hτ).Fiber q
abbrev MixedTotal := (mixedCore τ hτ).TotalSpace
instance mixedFiberBundle : FiberBundle ℂ (MixedFiber τ hτ) := (mixedCore τ hτ).fiberBundle
instance mixedVectorBundle : VectorBundle ℂ ℂ (MixedFiber τ hτ) := (mixedCore τ hτ).vectorBundle

@[expose] def sectionRatio (a : Index) (q : Base τ) : ℂ :=
  (levelSection τ hτ 3 a.1 q).2/(levelSection τ hτ 2 a.2 q).2
lemma sectionRatio_ne (a : Index) (q : Base τ) (hq : q∈domain τ hτ a) : sectionRatio τ hτ a q≠0 :=
  div_ne_zero (coordinate_ne τ hτ 1 q a.1 hq.1) (coordinate_ne τ hτ 0 q a.2 hq.2)

lemma transition_ratio (a b : Index) (q : Base τ)
    (ha : q∈domain τ hτ a) (hb : q∈domain τ hτ b) :
    transition τ hτ a b q=sectionRatio τ hτ a q/sectionRatio τ hτ b q := by
  change ((levelSection τ hτ 3 a.1 q).2/(levelSection τ hτ 3 b.1 q).2)/
      ((levelSection τ hτ 2 a.2 q).2/(levelSection τ hτ 2 b.2 q).2) =
    ((levelSection τ hτ 3 a.1 q).2/(levelSection τ hτ 2 a.2 q).2)/
      ((levelSection τ hτ 3 b.1 q).2/(levelSection τ hτ 2 b.2 q).2)
  field_simp [coordinate_ne τ hτ 1 q a.1 ha.1,coordinate_ne τ hτ 1 q b.1 hb.1,
    coordinate_ne τ hτ 0 q a.2 ha.2,coordinate_ne τ hτ 0 q b.2 hb.2]

@[expose] def denominator (q : Base τ) : ℂ := sectionRatio τ hτ ((mixedCore τ hτ).indexAt q) q
lemma denominator_ne (q : Base τ) : denominator τ hτ q≠0 :=
  sectionRatio_ne τ hτ _ q ((mixedCore τ hτ).mem_baseSet_at q)

/-- A literal complex-linear identification of the ORIGINAL degree-one
polarization fiber with the independently constructed quotient fiber. -/
@[expose] def fiberEquivalence (q : Base τ) :
    PELOriginalPolarizationLineBundle318.Fiber τ hτ q ≃ₗ[ℂ] MixedFiber τ hτ q where
  toFun v := v/denominator τ hτ q
  invFun w := denominator τ hτ q*w
  left_inv v := by field_simp [denominator_ne τ hτ q]
  right_inv w := by field_simp [denominator_ne τ hτ q]
  map_add' v w := add_div _ _ _
  map_smul' c v := by change (c*v)/_=c*(v/_); ring

lemma target_coordinate (q : Base τ) (a : Index) (ha : q∈domain τ hτ a)
    (v : PELOriginalPolarizationLineBundle318.Fiber τ hτ q) :
    ((mixedCore τ hτ).localTriv a ⟨q,fiberEquivalence τ hτ q v⟩).2=v/sectionRatio τ hτ a q := by
  change transition τ hτ ((mixedCore τ hτ).indexAt q) a q*(v/denominator τ hτ q)=_
  rw [transition_ratio τ hτ _ a q ((mixedCore τ hτ).mem_baseSet_at q) ha]
  change (denominator τ hτ q/sectionRatio τ hτ a q)*(v/denominator τ hτ q)=_
  field_simp [denominator_ne τ hτ q,sectionRatio_ne τ hτ a q ha]

/-- The original local transition appears to power ONE, because the
actual degree-three and degree-two section gauges cancel as t³/t²=t. -/
theorem original_chart_ratio (b : ComplexVectors) (q : Base τ)
    (hb : q∈PELOriginalPolarizationTransitions318.baseSet τ hτ b)
    (a : Index) (ha : q∈domain τ hτ a)
    (v : PELOriginalPolarizationLineBundle318.Fiber τ hτ q) :
    ((mixedCore τ hτ).localTriv a ⟨q,fiberEquivalence τ hτ q v⟩).2 =
      ((PELOriginalPolarizationLineBundle318.core τ hτ).localTriv b ⟨q,v⟩).2 /
        (PELOriginalHyperplanePullbackTopology318.sectionCoefficient τ hτ 1 b a.1 q /
          PELOriginalHyperplanePullbackTopology318.sectionCoefficient τ hτ 0 b a.2 q) := by
  rw [target_coordinate τ hτ q a ha]
  let t := PELOriginalPolarizationTransitions318.transition τ hτ
    ((PELOriginalPolarizationLineBundle318.core τ hτ).indexAt q) b q
  have ht : t≠0 := PELOriginalPolarizationTransitions318.transition_nonzero τ hτ _ _ _
  change ((v : ℂ)/((levelSection τ hτ 3 a.1 q).2/(levelSection τ hτ 2 a.2 q).2)) =
    (t*v)/((t^3*(levelSection τ hτ 3 a.1 q).2)/(t^2*(levelSection τ hτ 2 a.2 q).2))
  field_simp [ht,coordinate_ne τ hτ 1 q a.1 ha.1,coordinate_ne τ hτ 0 q a.2 ha.2]
  <;> ring
end PELOriginalDegreeOneRatioBundle318
