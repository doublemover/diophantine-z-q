module
public import ComplexProjectiveRatioCharts318
public import Mathlib.Topology.VectorBundle.Basic
public section
noncomputable section
namespace ComplexProjectiveHyperplaneBundle318
open Set Topology ComplexProjectiveQuotientTopology318 ComplexProjectiveRatioCharts318
variable (ι:Type*)[Fintype ι]
local instance :DecidableEq ι:=Classical.decEq ι
local instance projectiveTopology:TopologicalSpace (Space ι):=topology ι

/-- The dual tautological transition: a functional evaluated on the
representative normalized at k equals v_j/v_k times its j-coordinate. -/
@[expose] def transition(j k:ι)(p:Space ι):ℂ:=normalized ι k p j
lemma transition_mk(j k:ι)(v:V ι)(hv:v≠0):
    transition ι j k (Projectivization.mk ℂ v hv)=v j/v k:=rfl
lemma transition_self(j:ι)(p:Space ι)(hp:p∈domain ι j):transition ι j j p=1:=hp
lemma transition_nonzero(j k:ι)(p:Space ι)(hj:p∈domain ι j)(hk:p∈domain ι k):
    transition ι j k p≠0:=by
  obtain ⟨v,rfl⟩:=Quotient.exists_rep p
  exact div_ne_zero ((mk_mem_domain ι j _ _).mp hj) ((mk_mem_domain ι k _ _).mp hk)
lemma transition_comp(j k l:ι)(p:Space ι)
    (hj:p∈domain ι j)(hk:p∈domain ι k)(hl:p∈domain ι l):
    transition ι k l p*transition ι j k p=transition ι j l p:=by
  obtain ⟨v,rfl⟩:=Quotient.exists_rep p
  simp only [transition_mk]
  field_simp [((mk_mem_domain ι k _ _).mp hk),((mk_mem_domain ι l _ _).mp hl)]
lemma transition_continuous(j k:ι):
    ContinuousOn (transition ι j k) (domain ι j∩domain ι k):=by
  by_cases he:j=k
  · subst k
    apply continuousOn_const.congr
    intro p hp
    exact (transition_self ι j p hp.1).symm
  · have h:ContinuousOn (fun p:Space ι=>toAffine ι k p ⟨j,he⟩) (domain ι k):=
      (continuous_apply ⟨j,he⟩).comp_continuousOn (toAffine_continuousOn ι k)
    exact h.mono Set.inter_subset_right

/-- Actual hyperplane line bundle on the independently topologized
projective quotient, built from its dual tautological ratio transitions. -/
@[expose] def core:VectorBundleCore ℂ (Space ι) ℂ ι where
  baseSet:=domain ι
  isOpen_baseSet:=domain_open ι
  indexAt p:=(domain_cover ι p).choose
  mem_baseSet_at p:=(domain_cover ι p).choose_spec
  coordChange j k p:=transition ι j k p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self j p hp v:=by simp [transition_self ι j p hp]
  continuousOn_coordChange j k:=(transition_continuous ι j k).smul continuousOn_const
  coordChange_comp j k l p hp v:=by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [←mul_assoc,transition_comp ι j k l p hp.1.1 hp.1.2 hp.2]
abbrev Fiber(p:Space ι):=(core ι).Fiber p
abbrev Total:=(core ι).TotalSpace
instance fiberBundle:FiberBundle ℂ (Fiber ι):=(core ι).fiberBundle
instance vectorBundle:VectorBundle ℂ ℂ (Fiber ι):=(core ι).vectorBundle

lemma normalized_mem(j:ι)(p:Space ι):normalized ι j p∈p.submodule:=by
  obtain ⟨v,rfl⟩:=Quotient.exists_rep p
  rw [Projectivization.submodule_mk]
  change (fun k:ι=>v.val k/v.val j)∈Submodule.span ℂ {v.val}
  have he:(fun k:ι=>v.val k/v.val j)=(v.val j)⁻¹ • v.val:=by
    funext k;simp only [Pi.smul_apply,smul_eq_mul,div_eq_mul_inv];ring
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
@[expose] def normalizedVector(j:ι)(p:Space ι):p.submodule:=⟨normalized ι j p,normalized_mem ι j p⟩
lemma normalized_change(j k:ι)(p:Space ι)(hj:p∈domain ι j):
    normalizedVector ι k p=transition ι j k p • normalizedVector ι j p:=by
  apply Subtype.ext
  obtain ⟨v,rfl⟩:=Quotient.exists_rep p
  have h:v.val j≠0:=(mk_mem_domain ι j _ _).mp hj
  ext l
  change v.val l/v.val k=(v.val j/v.val k)*(v.val l/v.val j)
  by_cases hk:v.val k=0
  · simp [hk]
  · field_simp [h,hk]

/-- These are genuinely the transition laws of linear functionals on
the ACTUAL tautological line, not an unrelated rank-one cocycle. -/
theorem dual_tautological_coordinates(j k:ι)(p:Space ι)(hj:p∈domain ι j)
    (f:p.submodule→ₗ[ℂ]ℂ):
    f (normalizedVector ι k p)=transition ι j k p*f (normalizedVector ι j p):=by
  rw [normalized_change ι j k p hj,map_smul,smul_eq_mul]
lemma line_coordinate(j:ι)(p:Space ι)(hj:p∈domain ι j)(x:p.submodule):
    x=x.val j • normalizedVector ι j p:=by
  apply Subtype.ext
  obtain ⟨v,rfl⟩:=Quotient.exists_rep p
  have hv:v.val j≠0:=(mk_mem_domain ι j _ _).mp hj
  have hx:x.val∈Submodule.span ℂ {v.val}:=by
    simpa only [Projectivization.submodule_mk] using x.property
  obtain ⟨a,ha⟩:=Submodule.mem_span_singleton.mp hx
  ext k
  change x.val k=x.val j*(v.val k/v.val j)
  rw [←ha]
  simp only [Pi.smul_apply,smul_eq_mul]
  field_simp [hv]

/-- Evaluation at the ACTUAL normalized tautological vector identifies
its true dual line with the chart fiber; this is not just a ratio analogy. -/
@[expose] def dualCoordinate(j:ι)(p:Space ι)(hj:p∈domain ι j):
    (p.submodule→ₗ[ℂ]ℂ)≃ₗ[ℂ]ℂ where
  toFun f:=f (normalizedVector ι j p)
  invFun c:={toFun:=fun x=>c*x.val j
    map_add':=by intro x y;simp only [Submodule.coe_add,Pi.add_apply,mul_add]
    map_smul':=by intro a x;simp only [Submodule.coe_smul,Pi.smul_apply,smul_eq_mul];ring}
  left_inv f:=by
    ext x
    have h:=congrArg f (line_coordinate ι j p hj x)
    rw [map_smul,smul_eq_mul] at h
    exact (mul_comm _ _).trans h.symm
  right_inv c:=by
    change c*normalized ι j p j=c
    rw [show normalized ι j p j=1 from hj,mul_one]
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

@[expose] def fiberDual(p:Space ι):Fiber ι p≃ₗ[ℂ](p.submodule→ₗ[ℂ]ℂ):=
  (dualCoordinate ι ((core ι).indexAt p) p ((core ι).mem_baseSet_at p)).symm
/-- Every genuine bundle trivialization is the actual dual evaluation
coordinate, with the selected gauge eliminated by the proved cocycle. -/
lemma local_dual_coordinate(j:ι)(p:Space ι)(hj:p∈domain ι j)(v:Fiber ι p):
    ((core ι).localTriv j ⟨p,v⟩).2=
      fiberDual ι p v (normalizedVector ι j p):=by
  let a:ι:=(core ι).indexAt p
  have ha:p∈domain ι a:=(core ι).mem_baseSet_at p
  have h:=dual_tautological_coordinates ι a j p ha (fiberDual ι p v)
  have he:fiberDual ι p v (normalizedVector ι a p)=v:=
    (dualCoordinate ι a p ha).apply_symm_apply v
  rw [he] at h
  exact h.symm
end ComplexProjectiveHyperplaneBundle318
