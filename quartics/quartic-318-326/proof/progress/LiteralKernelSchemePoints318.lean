module
public import LiteralTriplingHom318
public import LiteralKernelNegation318
public import Mathlib.Algebra.Group.TransferInstance
public section
noncomputable section
namespace LiteralKernelSchemePoints318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {T:Scheme}
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD
@[expose] def inclusion : K ⟶ WeierstrassGluing318.scheme A B:=pullback.fst _ _
@[expose] def structureMap : K ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)):=pullback.snd _ _
@[reassoc] theorem inclusion_base : inclusion N ≫ WeierstrassGluing318.structureMap A B=structureMap N := by
  have h:=congrArg (fun f=>f ≫ WeierstrassGluing318.structureMap A B)
    (pullback.condition (f:=CompletedIteratedAddition318.tripling A B hD) (g:=WeierstrassGluing318.infinity A B))
  simpa only [inclusion,structureMap,Category.assoc,CompletedIteratedAddition318.tripling_over_base,
    WeierstrassGluing318.infinity_section,Category.comp_id] using h
@[reassoc] theorem inclusion_tripling : inclusion N ≫ CompletedIteratedAddition318.tripling A B hD=
    structureMap N ≫ WeierstrassGluing318.infinity A B:=pullback.condition
variable (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
@[expose] def Points := {f:T ⟶ K // f ≫ structureMap N=b}
@[expose] def intoCurve (p:Points N b) : LiteralSchemePointOperations318.Points N b:=
  ⟨p.val ≫ inclusion N,by rw [Category.assoc,inclusion_base];exact p.property⟩

@[expose] def toKilled (p:Points N b) : LiteralTriplingHom318.killed N b :=
  ⟨intoCurve N b p,by
    rw [LiteralTriplingHom318.mem_killed]
    apply Subtype.ext
    rw [LiteralTriplingHom318.three_value]
    change (p.val ≫ inclusion N) ≫ CompletedIteratedAddition318.tripling A B hD=b ≫ WeierstrassGluing318.infinity A B
    rw [Category.assoc,inclusion_tripling,←Category.assoc,p.property]⟩
lemma killed_relation (p:LiteralTriplingHom318.killed N b) :
    p.val.val ≫ CompletedIteratedAddition318.tripling A B hD=b ≫ WeierstrassGluing318.infinity A B:=by
  have h:3 • p.val=0:=p.property
  have hh:=congrArg Subtype.val h
  rw [LiteralTriplingHom318.three_value] at hh
  exact hh
@[expose] def fromKilled (p:LiteralTriplingHom318.killed N b) : Points N b:=
  ⟨pullback.lift p.val.val b (killed_relation N b p),by simp only [structureMap,pullback.lift_snd]⟩
@[simp] theorem from_to (p:Points N b) : fromKilled N b (toKilled N b p)=p:=by
  apply Subtype.ext
  apply pullback.hom_ext
  · simp only [fromKilled,pullback.lift_fst]
    rfl
  · simp only [fromKilled,pullback.lift_snd]
    exact p.property.symm
@[simp] theorem to_from (p:LiteralTriplingHom318.killed N b) : toKilled N b (fromKilled N b p)=p:=by
  apply Subtype.ext
  apply Subtype.ext
  change (pullback.lift p.val.val b (killed_relation N b p)) ≫ pullback.fst _ _=p.val.val
  exact pullback.lift_fst _ _ _
/-- The actual tripling fiber represents exactly the intrinsic three-killed
subgroup on every Scheme test, with both explicit inverse identities. -/
@[expose] def equiv : Points N b ≃ LiteralTriplingHom318.killed N b where
  toFun:=toKilled N b
  invFun:=fromKilled N b
  left_inv:=from_to N b
  right_inv:=to_from N b

instance group : AddCommGroup (Points N b):=(equiv N b).addCommGroup
@[expose] def addEquiv : Points N b ≃+ LiteralTriplingHom318.killed N b where
  __:=equiv N b
  map_add' p q:=(equiv N b).apply_symm_apply _
@[expose] def embedding : Points N b →+ LiteralSchemePointOperations318.Points N b:=
  (LiteralTriplingHom318.killed N b).subtype.comp (addEquiv N b).toAddMonoidHom
@[simp] theorem embedding_apply (p:Points N b) : embedding N b p=intoCurve N b p:=rfl
lemma embedding_injective : Function.Injective (embedding N b):=by
  intro p q h
  apply (equiv N b).injective
  apply Subtype.ext
  exact h
end LiteralKernelSchemePoints318
