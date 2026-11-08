module
public import PushforwardStructureSheaf318
public section
noncomputable section
namespace AffineSpecFreePushforward318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S:CommRingCat.{u}) [Algebra R S]
abbrev ringMap:R⟶S:=CommRingCat.ofHom (algebraMap R S)
abbrev object: (Spec R).Modules:=PushforwardStructureSheaf318.object (Spec.map (ringMap R S))
/-- The actual global sections of the pushed-forward structure sheaf identify
with the original S as an R-module through the literal ring map f. -/
@[expose] def globalsEquiv:moduleSpecΓFunctor.obj (object R S)≃ₗ[R]S where
  toFun:=(Scheme.ΓSpecIso S).hom
  invFun:=(Scheme.ΓSpecIso S).inv
  left_inv s:=by exact congrArg (fun g=>g s) (Scheme.ΓSpecIso S).hom_inv_id
  right_inv s:=by exact congrArg (fun g=>g s) (Scheme.ΓSpecIso S).inv_hom_id
  map_add' s t:=(Scheme.ΓSpecIso S).hom.hom.map_add s t
  map_smul' a s:=by
    change (Scheme.ΓSpecIso S).hom
      ((Spec.map (ringMap R S)).appTop ((Spec R).presheaf.map (𝟙 (op ⊤)) ((Scheme.ΓSpecIso R).inv a))*(show Γ(Spec S,⊤) from s))=_
    simp only [map_mul, RingHom.id_apply, Algebra.smul_def]
    have hi := congrArg (fun g:Γ(Spec R,⊤)⟶Γ(Spec R,⊤)=>g ((Scheme.ΓSpecIso R).inv a))
      ((Spec R).presheaf.map_id (op ⊤))
    rw [hi]
    have h:=congrArg (fun g:Γ(Spec R,⊤)⟶S=>g ((Scheme.ΓSpecIso R).inv a))
      (Scheme.ΓSpecIso_naturality (ringMap R S))
    change _ = algebraMap R S a * (Scheme.ΓSpecIso S).hom s
    congr 1
    simpa only [CommRingCat.comp_apply, CommRingCat.hom_inv_apply, CommRingCat.id_apply, ringMap, CommRingCat.hom_ofHom] using h
/-- The actual affine pushforward has its usual tilde/global-sections comparison. -/
lemma fromTilde_isIso:IsIso (object R S).fromTildeΓ:=
  isIso_fromTildeΓ_pushforward (ringMap R S) (SheafOfModules.unit (Spec S).ringCatSheaf)
/-- A finite-free algebra basis gives a genuine free O_Spec(R)-sheaf
isomorphism to the original pushed-forward structure sheaf. -/
@[expose] def iso {ι:Type u} (bs:Module.Basis ι R S):
    SheafOfModules.free (R:=(Spec R).ringCatSheaf) ι≅object R S:=by
  letI:=fromTilde_isIso R S
  exact (tildeFinsupp (R:=R) ι).symm ≪≫
    (tilde.functor R).mapIso (bs.repr.symm.trans (globalsEquiv R S).symm).toModuleIso ≪≫
      asIso (object R S).fromTildeΓ
lemma iso_hom_inv {ι:Type u} (bs:Module.Basis ι R S):
    (iso R S bs).hom≫(iso R S bs).inv=𝟙 _ :=(iso R S bs).hom_inv_id
lemma iso_inv_hom {ι:Type u} (bs:Module.Basis ι R S):
    (iso R S bs).inv≫(iso R S bs).hom=𝟙 _ :=(iso R S bs).inv_hom_id
end AffineSpecFreePushforward318
