module
public import ComplexProjectiveQuotientTopology318
public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public section
noncomputable section
namespace ComplexProjectiveRatioCharts318
open Set Topology ComplexProjectiveQuotientTopology318
variable (ι:Type*) [Fintype ι]
local instance :DecidableEq ι:=Classical.decEq ι
local instance projectiveTopology:TopologicalSpace (Space ι):=topology ι
abbrev Affine (j:ι):=({i:ι // i≠j}→ℂ)
@[expose] def embed (j:ι)(w:Affine ι j):V ι:=fun i=>if h:i=j then 1 else w ⟨i,h⟩
lemma embed_at (j:ι)(w:Affine ι j):embed ι j w j=1:=by simp [embed]
lemma embed_other (j:ι)(w:Affine ι j)(i:{i:ι //i≠j}):embed ι j w i=w i:=by
  simp [embed,i.property]
lemma embed_nonzero (j:ι)(w:Affine ι j):embed ι j w≠0:=by
  intro h
  have he:=congrFun h j
  rw [embed_at] at he
  exact one_ne_zero he
@[expose] def fromAffine (j:ι)(w:Affine ι j):Space ι:=
  Projectivization.mk ℂ (embed ι j w) (embed_nonzero ι j w)
@[expose] def toAffine (j:ι)(p:Space ι):Affine ι j:=fun i=>normalized ι j p i.val
lemma fromAffine_mem (j:ι)(w:Affine ι j):fromAffine ι j w∈domain ι j:=by
  apply (mk_mem_domain ι j _ _).mpr
  rw [embed_at]
  exact one_ne_zero
lemma to_from (j:ι)(w:Affine ι j):toAffine ι j (fromAffine ι j w)=w:=by
  funext i
  simp only [toAffine,fromAffine,normalized_mk,embed_at,embed_other,div_one]
lemma from_to (j:ι)(p:Space ι)(hp:p∈domain ι j):fromAffine ι j (toAffine ι j p)=p:=by
  obtain ⟨v,rfl⟩:=Quotient.exists_rep p
  have hj:v.val j≠0:=(mk_mem_domain ι j v.val v.property).mp hp
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨(v.val j)⁻¹,?_⟩
  funext i
  by_cases hi:i=j
  · subst i
    simp only [Pi.smul_apply,smul_eq_mul,embed_at]
    exact inv_mul_cancel₀ hj
  · simp only [Pi.smul_apply,smul_eq_mul,embed,dif_neg hi,toAffine,normalized_mk]
    rw [div_eq_mul_inv,mul_comm]
lemma embed_continuous (j:ι):Continuous (embed ι j):=by
  apply continuous_pi
  intro i
  by_cases hi:i=j
  · simp only [embed,dif_pos hi]
    exact continuous_const
  · simp only [embed,dif_neg hi]
    exact continuous_apply ⟨i,hi⟩
lemma fromAffine_continuous (j:ι):Continuous (fromAffine ι j):=
  continuous_mk ι (embed ι j) (embed_continuous ι j) (embed_nonzero ι j)
lemma toAffine_continuousOn (j:ι):ContinuousOn (toAffine ι j) (domain ι j):=by
  apply ((quotientMap ι).continuousOn_isOpen_iff (domain_open ι j)).mpr
  intro v hv
  have hj:v.val j≠0:=(mk_mem_domain ι j v.val v.property).mp hv
  apply continuousWithinAt_pi.mpr
  intro i
  change ContinuousWithinAt (fun w:NonzeroVectors ι=>w.val i.val/w.val j)
    ((Projectivization.mk' ℂ:NonzeroVectors ι→Space ι) ⁻¹' domain ι j) v
  exact (((continuous_apply i.val).comp continuous_subtype_val).continuousAt.div
    (((continuous_apply j).comp continuous_subtype_val).continuousAt) hj).continuousWithinAt

/-- Genuine standard affine-ratio chart of the independently defined
quotient projective space. Its inverse uses coordinate j=1 and retains all
other coordinates; domain and both maps have their actual topologies. -/
@[expose] def chart (j:ι):OpenPartialHomeomorph (Space ι) (Affine ι j) where
  toFun:=toAffine ι j
  invFun:=fromAffine ι j
  source:=domain ι j
  target:=Set.univ
  map_source':=fun _ _=>Set.mem_univ _
  map_target':=fun w _=>fromAffine_mem ι j w
  left_inv':=fun p hp=>from_to ι j p hp
  right_inv':=fun w _=>to_from ι j w
  open_source:=domain_open ι j
  open_target:=isOpen_univ
  continuousOn_toFun:=toAffine_continuousOn ι j
  continuousOn_invFun:=(fromAffine_continuous ι j).continuousOn

lemma transition_formula (j k:ι)(w:Affine ι j)(i:{i:ι //i≠k}):
    chart ι k ((chart ι j).symm w) i=embed ι j w i.val/embed ι j w k:=rfl
lemma overlap_iff (j k:ι)(w:Affine ι j):
    (chart ι j).symm w∈(chart ι k).source↔embed ι j w k≠0:=
  mk_mem_domain ι k _ _
end ComplexProjectiveRatioCharts318
