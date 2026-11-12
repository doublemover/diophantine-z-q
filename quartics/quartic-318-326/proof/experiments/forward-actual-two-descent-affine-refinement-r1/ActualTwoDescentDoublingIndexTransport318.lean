module
public import ActualTwoDescentActualTwoTorsionCardinality318
public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public section
noncomputable section
namespace ActualTwoDescentDoublingIndexTransport318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

abbrev doubles (A : Type*) [AddCommGroup A] := (nsmulAddMonoidHom (α:=A) 2).range
abbrev doubleKernel (A : Type*) [AddCommGroup A] := (nsmulAddMonoidHom (α:=A) 2).ker

lemma actual_doubles_map_equiv (e : A ≃+ B) : (doubles A).map e.toAddMonoidHom=doubles B := by
  ext b
  constructor
  · rintro ⟨a,⟨x,hx⟩,rfl⟩
    refine ⟨e x,?_⟩
    change 2 • e x=e a
    rw [←e.map_nsmul]
    exact congrArg e hx
  · rintro ⟨b,rfl⟩
    refine ⟨2 • e.symm b,⟨e.symm b,rfl⟩,?_⟩
    change e (2 • e.symm b)=2 • b
    rw [e.map_nsmul,e.apply_symm_apply]

lemma actual_doubles_index_equiv (e : A ≃+ B) : (doubles A).index=(doubles B).index := by
  rw [←actual_doubles_map_equiv e]
  exact (AddSubgroup.index_map_equiv (doubles A) e).symm

def doubleKernelEquiv (e : A ≃+ B) : doubleKernel A ≃ doubleKernel B where
  toFun a := ⟨e a,by
    change 2 • e (a : A)=0
    have ha : 2 • (a : A)=0 := a.property
    rw [←e.map_nsmul,ha,e.map_zero]⟩
  invFun b := ⟨e.symm b,by
    change 2 • e.symm (b : B)=0
    have hb : 2 • (b : B)=0 := b.property
    rw [←e.symm.map_nsmul,hb,e.symm.map_zero]⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)

lemma actual_doubles_prod : doubles (A × B)=(doubles A).prod (doubles B) := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    exact ⟨⟨q.1,rfl⟩,⟨q.2,rfl⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨(a,b),Prod.ext ha hb⟩

def doubleKernelProdEquiv : doubleKernel (A × B) ≃ doubleKernel A × doubleKernel B where
  toFun p := (⟨p.val.1,congrArg Prod.fst p.property⟩,⟨p.val.2,congrArg Prod.snd p.property⟩)
  invFun p := ⟨(p.1.val,p.2.val),Prod.ext p.1.property p.2.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv p := by apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- The additive doubling index agrees with the previously used actual
multiplicative-tag quotient, without replacing its underlying group. -/
lemma actual_tagged_doubles_index (A : Type*) [AddCommGroup A] :
    (doubles A).index=Nat.card (Multiplicative A ⧸ (powMonoidHom (α:=Multiplicative A) 2).range) := by
  have he : (doubles A).toSubgroup=(powMonoidHom (α:=Multiplicative A) 2).range := by
    ext a
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨Multiplicative.ofAdd x,?_⟩
      rw [powMonoidHom_apply,pow_two]
      have h : x+x=a.toAdd := by simpa only [nsmulAddMonoidHom_apply,two_nsmul] using hx
      exact congrArg Multiplicative.ofAdd h
    · rintro ⟨x,hx⟩
      refine ⟨x.toAdd,?_⟩
      have h := congrArg Multiplicative.toAdd hx
      simpa only [powMonoidHom_apply,pow_two,Multiplicative.toAdd_mul,nsmulAddMonoidHom_apply,two_nsmul] using h
  rw [←AddSubgroup.index_toSubgroup,he,Subgroup.index_eq_card]

end ActualTwoDescentDoublingIndexTransport318
