module
public import PELOriginalBalancedThetaProducts318
public section
noncomputable section
namespace PELOriginalPolarizationPowerBundle318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationAutomorphy318
open PELOriginalPolarizationLineBundle318 Filter Topology
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=
  PELOriginalPeriodLattice318.original_discrete τ hτ

/-- Power of the ORIGINAL line cocycle on the SAME original atlas.
The base, selected gauges and all original transitions are retained. -/
@[expose] def powerCore (n:ℕ):VectorBundleCore ℂ (Base τ) ℂ ComplexVectors where
  baseSet:=(core τ hτ).baseSet
  isOpen_baseSet:=(core τ hτ).isOpen_baseSet
  indexAt:=(core τ hτ).indexAt
  mem_baseSet_at:=(core τ hτ).mem_baseSet_at
  coordChange a b q:=transition τ hτ a b q^n • ContinuousLinearMap.id ℂ ℂ
  coordChange_self a q _ v:=by simp [transition_self]
  continuousOn_coordChange a b:=
    ((transition_continuous τ hτ a b).pow n).smul continuousOn_const
  coordChange_comp a b c q hq v:=by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [←mul_assoc,←mul_pow,transition_comp τ hτ a b c q hq.1.1 hq.1.2 hq.2]
abbrev PowerFiber (n:ℕ) (q:Base τ):Type:=(powerCore τ hτ n).Fiber q
abbrev PowerTotal (n:ℕ):Type:=(powerCore τ hτ n).TotalSpace
instance power_fiberBundle (n:ℕ):FiberBundle ℂ (PowerFiber τ hτ n):=
  (powerCore τ hτ n).fiberBundle
instance power_vectorBundle (n:ℕ):VectorBundle ℂ ℂ (PowerFiber τ hτ n):=
  (powerCore τ hτ n).vectorBundle
lemma rank_one (n:ℕ) (q:Base τ):Module.finrank ℂ (PowerFiber τ hτ n q)=1:=by
  exact Module.finrank_self ℂ
lemma first_transition (a b:ComplexVectors) (q:Base τ):
    (powerCore τ hτ 1).coordChange a b q=(core τ hτ).coordChange a b q:=by
  simp only [powerCore,core,pow_one]

/-- Local tensor multiplication is compatible with the ACTUAL original
line transitions. Thus these are powers of that cocycle, not unrelated
lines merely sharing the same base or rank. -/
lemma tensor_transition (n:ℕ) (a b:ComplexVectors) (q:Base τ) (v:Fin n→ℂ):
    (∏j,(core τ hτ).coordChange a b q (v j))=
      (powerCore τ hτ n).coordChange a b q (∏j,v j):=by
  classical
  simp [powerCore,core,Finset.prod_mul_distrib]
lemma multiplication_transition (m n:ℕ) (a b:ComplexVectors) (q:Base τ) (u v:ℂ):
    (powerCore τ hτ m).coordChange a b q u*
      (powerCore τ hτ n).coordChange a b q v=
        (powerCore τ hτ (m+n)).coordChange a b q (u*v):=by
  simp only [powerCore,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul,pow_add]
  ring

@[expose] def powerSection (n:ℕ) (f:ComplexVectors→ℂ) (q:Base τ):PowerTotal τ hτ n:=
  ⟨q,f (chart τ hτ ((core τ hτ).indexAt q) q)⟩
lemma projects (n:ℕ) (f:ComplexVectors→ℂ) (q:Base τ):
    (powerSection τ hτ n f q).1=q:=rfl
lemma local_formula (n:ℕ) (f:ComplexVectors→ℂ)
    (hf:∀l:L τ hτ,∀z,f (z+l.val)=factor τ hτ l z^n*f z)
    (a:ComplexVectors) (q:Base τ) (ha:q∈baseSet τ hτ a):
    (powerCore τ hτ n).localTriv a (powerSection τ hτ n f q)=
      (q,f (chart τ hτ a q)):=by
  apply Prod.ext
  · rfl
  · let b:ComplexVectors:=(core τ hτ).indexAt q
    have hb:q∈baseSet τ hτ b:=(core τ hτ).mem_baseSet_at q
    have hs:chart τ hτ b q+(shift τ hτ b a q:ComplexVectors)=chart τ hτ a q:=by
      rw [shift_value τ hτ b a q hb ha];abel
    have h:=hf (shift τ hτ b a q) (chart τ hτ b q)
    rw [hs] at h
    exact h.symm
lemma continuous_section (n:ℕ) (f:ComplexVectors→ℂ) (hc:Continuous f)
    (hf:∀l:L τ hτ,∀z,f (z+l.val)=factor τ hτ l z^n*f z):
    Continuous (powerSection τ hτ n f):=by
  apply continuous_iff_continuousAt.mpr
  intro q
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at q
  apply ((powerCore τ hτ n).localTriv a).continuousAt_of_comp_left continuousAt_id ha
  have h:ContinuousAt (fun r:Base τ=>(r,f (chart τ hτ a r))) q:=
    continuousAt_id.prodMk (hc.continuousAt.comp q ((chart τ hτ a).continuousAt ha))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chart τ hτ a).open_source.mem_nhds ha] with r hr
  exact (local_formula τ hτ n f hf a r hr).symm
lemma coordinate_formula (n:ℕ) (f:ComplexVectors→ℂ)
    (hf:∀l:L τ hτ,∀z,f (z+l.val)=factor τ hτ l z^n*f z)
    (a z:ComplexVectors) (hz:z∈(chart τ hτ a).target):
    ((powerCore τ hτ n).localTriv a
      (powerSection τ hτ n f (projection (P τ) z))).2=f z:=by
  have hq:projection (P τ) z∈baseSet τ hτ a:=by
    simpa only [chart,localChart_symm] using (chart τ hτ a).map_target hz
  rw [local_formula τ hτ n f hf a _ hq]
  have he:chart τ hτ a (projection (P τ) z)=z:=by
    simpa only [chart,localChart_symm] using (chart τ hτ a).right_inv hz
  exact congrArg f he
lemma holomorphic_section (n:ℕ) (f:ComplexVectors→ℂ) (hd:Differentiable ℂ f)
    (hf:∀l:L τ hτ,∀z,f (z+l.val)=factor τ hτ l z^n*f z) (a:ComplexVectors):
    DifferentiableOn ℂ (fun z:ComplexVectors=>((powerCore τ hτ n).localTriv a
      (powerSection τ hτ n f (projection (P τ) z))).2) (chart τ hτ a).target:=by
  apply hd.differentiableOn.congr
  intro z hz
  exact coordinate_formula τ hτ n f hf a z hz
end PELOriginalPolarizationPowerBundle318
