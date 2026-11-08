module
public import IntrinsicGlobalFrame318
public section
noncomputable section
namespace IntrinsicGlobalInvariantGenerator318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 450000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R:Type u} [CommRing R] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
lemma frame_inv_apply (a:Γ(WeierstrassGluing318.scheme A B,⊤)):
    (IntrinsicGlobalFrame318.frame A B hD).inv.val.app (op ⊤) a=
      a • IntrinsicGlobalFrame318.invariant A B hD:=by
  change (ModuleGlobalSections318.ofTop _ (IntrinsicGlobalFrame318.invariant A B hD)).val.app (op ⊤) a=_
  rw [ModuleGlobalSections318.ofTop_apply]
  change a • (FamilyIntrinsicDifferentials318.familyOmega A B).presheaf.map (𝟙 (op ⊤))
    (IntrinsicGlobalFrame318.invariant A B hD)=_
  rw [CategoryTheory.Functor.map_id,ConcreteCategory.id_apply]
/-- The specified global invariant, not an unspecified basis vector,
freely generates all global intrinsic differential sections over the actual
global section ring. -/
theorem bijective:Function.Bijective (fun a:Γ(WeierstrassGluing318.scheme A B,⊤)=>
    a • IntrinsicGlobalFrame318.invariant A B hD):=by
  have h:=ConcreteCategory.bijective_of_isIso ((IntrinsicGlobalFrame318.frame A B hD).inv.app ⊤)
  change Function.Bijective (fun a:Γ(WeierstrassGluing318.scheme A B,⊤)=>
    (IntrinsicGlobalFrame318.frame A B hD).inv.val.app (op ⊤) a) at h
  have he:(fun a:Γ(WeierstrassGluing318.scheme A B,⊤)=>
      (IntrinsicGlobalFrame318.frame A B hD).inv.val.app (op ⊤) a)=
    (fun a=>a • IntrinsicGlobalFrame318.invariant A B hD):=funext (frame_inv_apply A B hD)
  rw [←he]
  exact h
end IntrinsicGlobalInvariantGenerator318
