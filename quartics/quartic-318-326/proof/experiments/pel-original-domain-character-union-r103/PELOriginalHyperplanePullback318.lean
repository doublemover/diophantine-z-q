module
public import ComplexProjectiveHyperplaneBundle318
public import PELOriginalAllLevelHolomorphicMap318
public section
noncomputable section
namespace PELOriginalHyperplanePullback318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelProjectiveMap318
open ComplexProjectiveQuotientTopology318
namespace HP
export ComplexProjectiveHyperplaneBundle318 (transition transition_comp transition_self transition_continuous transition_nonzero)
end HP
variable (τ:ℂ)(hτ:0<τ.im)(n:ℕ)
local instance targetTopology:TopologicalSpace (Space (Label (n+2))):=topology (Label (n+2))
local notation "M" => projectiveMap τ hτ n
local notation "H" => ComplexProjectiveHyperplaneBundle318.core (Label (n+2))

/-- Literal pullback of the independently built hyperplane cocycle
along the SAME actual all-level projective map. -/
@[expose] def pullbackCore:VectorBundleCore ℂ (Base τ) ℂ (Label (n+2)) where
  baseSet j:=M ⁻¹' H.baseSet j
  isOpen_baseSet j:=(H.isOpen_baseSet j).preimage
    (PELOriginalAllLevelHolomorphicMap318.original_continuous τ hτ n)
  indexAt q:=H.indexAt (M q)
  mem_baseSet_at q:=H.mem_baseSet_at (M q)
  coordChange j k q:=H.coordChange j k (M q)
  coordChange_self j q hq v:=H.coordChange_self j (M q) hq v
  continuousOn_coordChange j k:=
    (H.continuousOn_coordChange j k).comp
      (PELOriginalAllLevelHolomorphicMap318.original_continuous τ hτ n).continuousOn
      (by intro q hq;exact hq)
  coordChange_comp j k l q hq v:=H.coordChange_comp j k l (M q) hq v
abbrev PullbackFiber(q:Base τ):=(pullbackCore τ hτ n).Fiber q
abbrev PullbackTotal:=(pullbackCore τ hτ n).TotalSpace
instance pullbackFiberBundle:FiberBundle ℂ (PullbackFiber τ hτ n):=(pullbackCore τ hτ n).fiberBundle
instance pullbackVectorBundle:VectorBundle ℂ ℂ (PullbackFiber τ hτ n):=(pullbackCore τ hτ n).vectorBundle

lemma coordinate_ne(q:Base τ)(j:Label (n+2))
    (hj:q∈(pullbackCore τ hτ n).baseSet j):
    (levelSection τ hτ (n+2) j q).2≠0:=
  (mk_mem_domain (Label (n+2)) j _ _).mp hj
@[expose] def denominator(q:Base τ):ℂ:=
  (levelSection τ hτ (n+2) (H.indexAt (M q)) q).2
lemma denominator_ne(q:Base τ):denominator τ hτ n q≠0:=
  coordinate_ne τ hτ n q _ ((pullbackCore τ hτ n).mem_baseSet_at q)

/-- Actual original power fiber → pulled-back hyperplane fiber. The
coefficient is divided by the selected ACTUAL nonzero section value;
this is the dual-tautological convention, not the opposite line. -/
@[expose] def fiberEquivalence(q:Base τ):
    PowerFiber τ hτ (n+2) q≃ₗ[ℂ]PullbackFiber τ hτ n q where
  toFun v:=v/denominator τ hτ n q
  invFun w:=denominator τ hτ n q*w
  left_inv v:=by field_simp [denominator_ne τ hτ n q]
  right_inv w:=by field_simp [denominator_ne τ hτ n q]
  map_add' v w:=add_div _ _ _
  map_smul' c v:=by change (c*v)/_=c*(v/_);ring

lemma target_coordinate(q:Base τ)(j:Label (n+2))
    (hj:q∈(pullbackCore τ hτ n).baseSet j)(v:PowerFiber τ hτ (n+2) q):
    ((pullbackCore τ hτ n).localTriv j ⟨q,fiberEquivalence τ hτ n q v⟩).2=
      v/(levelSection τ hτ (n+2) j q).2:=by
  change (denominator τ hτ n q/(levelSection τ hτ (n+2) j q).2)*
    (v/denominator τ hτ n q)=_
  field_simp [denominator_ne τ hτ n q,coordinate_ne τ hτ n q j hj]

/-- Exact comparison in EVERY genuine original line chart and target
hyperplane chart: pulled-back coefficient equals original coefficient
DIVIDED BY the same original section coefficient. All selected gauges
cancel by the actual power-cocycle transition. -/
theorem original_chart_ratio(a:ComplexVectors)(q:Base τ)
    (ha:q∈baseSet τ hτ a)(j:Label (n+2))
    (hj:q∈(pullbackCore τ hτ n).baseSet j)(v:PowerFiber τ hτ (n+2) q):
    ((pullbackCore τ hτ n).localTriv j ⟨q,fiberEquivalence τ hτ n q v⟩).2=
      ((powerCore τ hτ (n+2)).localTriv a ⟨q,v⟩).2/
        ((powerCore τ hτ (n+2)).localTriv a (levelSection τ hτ (n+2) j q)).2:=by
  rw [target_coordinate τ hτ n q j hj v]
  let t:=transition τ hτ ((core τ hτ).indexAt q) a q^(n+2)
  have ht:t≠0:=pow_ne_zero _ (transition_nonzero τ hτ _ _ _)
  change v/(levelSection τ hτ (n+2) j q).2=
    (t*v)/(t*(levelSection τ hτ (n+2) j q).2)
  field_simp [ht,coordinate_ne τ hτ n q j hj]
end PELOriginalHyperplanePullback318
