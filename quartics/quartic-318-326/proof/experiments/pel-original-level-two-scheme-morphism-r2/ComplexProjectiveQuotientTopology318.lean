module
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.ContinuousOn
public import Mathlib.Analysis.Complex.Basic
public section
noncomputable section
namespace ComplexProjectiveQuotientTopology318
open Set Topology
variable (ι:Type*) [Fintype ι]
abbrev V:=ι→ℂ
abbrev Space:=Projectivization ℂ (V ι)
abbrev NonzeroVectors:={v:V ι // v≠0}

/-- The canonical quotient topology on the ACTUAL algebraic
projectivization, not a topology transported from our original torus.
The quotient-topology construction follows the public mathlib approach
of Zayn Blore (2026), commit d868575a9b9f952db89bb4315b99497bbd078440,
proved here against this project's pinned older Projectivization API. -/
@[expose] def topology:TopologicalSpace (Space ι):=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid ℂ (V ι))))
local instance projectiveTopology:TopologicalSpace (Space ι):=topology ι
lemma quotientMap:IsQuotientMap (Projectivization.mk' ℂ:NonzeroVectors ι→Space ι):=
  isQuotientMap_quotient_mk'
lemma continuous_mk':Continuous (Projectivization.mk' ℂ:NonzeroVectors ι→Space ι):=
  continuous_quotient_mk'
lemma continuous_mk {X:Type*}[TopologicalSpace X](f:X→V ι)
    (hf:Continuous f)(hn:∀x,f x≠0):
    Continuous (fun x=>Projectivization.mk ℂ (f x) (hn x)):=
  (continuous_mk' ι).comp (hf.subtype_mk hn)

@[expose] def normalized (j:ι)(p:Space ι):V ι:=
  Projectivization.lift (fun v:NonzeroVectors ι=>fun i=>v.val i/v.val j)
    (by
      intro v w t he
      have ht:t≠0:=by
        intro ht
        apply v.property
        simpa only [ht,zero_smul] using he
      funext i
      have hi:=congrFun he i
      have hj:=congrFun he j
      simp only [Pi.smul_apply,smul_eq_mul] at hi hj
      rw [hi,hj]
      by_cases hw:w.val j=0
      · simp [hw]
      · field_simp [ht,hw]) p
@[simp] lemma normalized_mk (j:ι)(v:V ι)(hv:v≠0):
    normalized ι j (Projectivization.mk ℂ v hv)=fun i=>v i/v j:=rfl
@[expose] def domain (j:ι):Set (Space ι):={p|normalized ι j p j=1}
lemma mk_mem_domain (j:ι)(v:V ι)(hv:v≠0):
    Projectivization.mk ℂ v hv∈domain ι j↔v j≠0:=by
  change v j/v j=1↔v j≠0
  constructor
  · intro h hz
    simp only [hz,div_zero] at h
    exact zero_ne_one h
  · exact div_self
lemma domain_open (j:ι):IsOpen (domain ι j):=by
  apply (quotientMap ι).isOpen_preimage.mp
  have he:(Projectivization.mk' ℂ:NonzeroVectors ι→Space ι) ⁻¹' domain ι j=
      {v:NonzeroVectors ι|v.val j≠0}:=by
    ext v
    exact mk_mem_domain ι j v.val v.property
  rw [he]
  exact isOpen_ne ((continuous_apply j).comp continuous_subtype_val) continuous_const
lemma domain_cover (p:Space ι):∃j,p∈domain ι j:=by
  have hp:=Projectivization.rep_nonzero p
  have he:∃j,Projectivization.rep p j≠0:=by
    by_contra h
    push_neg at h
    exact hp (funext h)
  obtain ⟨j,hj⟩:=he
  refine ⟨j,?_⟩
  rw [←Projectivization.mk_rep p]
  exact (mk_mem_domain ι j _ _).mpr hj
end ComplexProjectiveQuotientTopology318
