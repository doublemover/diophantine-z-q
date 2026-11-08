module
public import PushforwardStructureSheaf318
public section
noncomputable section
namespace OpenPullbackStructure318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {P X U Y:Scheme.{u}} (q:P⟶U) (k:P⟶X) (j:U⟶Y) (f:X⟶Y)
    [IsOpenImmersion k] [IsOpenImmersion j] (H:IsPullback q k j f)
include H
lemma opens_eq (W:U.Opens):k ''ᵁ(q⁻¹ᵁW)=f⁻¹ᵁ(j ''ᵁW):=
  IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H W
lemma inclusion (W:U.Opens):q⁻¹ᵁW≤k⁻¹ᵁ(f⁻¹ᵁ(j ''ᵁW)):=by
  rw [←opens_eq q k j f H W,Scheme.Hom.preimage_image_eq]
/-- Actual section comparison for an open cartesian square. -/
@[expose] def ringIso (W:U.Opens):Γ(X,f⁻¹ᵁ(j ''ᵁW))≅Γ(P,q⁻¹ᵁW):=
  X.presheaf.mapIso (eqToIso (opens_eq q k j f H W)).op ≪≫k.appIso (q⁻¹ᵁW)
lemma ringIso_hom (W:U.Opens):
    (ringIso q k j f H W).hom=k.appLE (f⁻¹ᵁ(j ''ᵁW)) (q⁻¹ᵁW) (inclusion q k j f H W):=by
  simp [ringIso,Scheme.Hom.appIso_hom',Scheme.Hom.map_appLE]
lemma scalar_square (W:U.Opens):
    f.app (j ''ᵁW)≫(ringIso q k j f H W).hom=(j.appIso W).hom≫q.app W:=by
  rw [ringIso_hom,Scheme.Hom.appIso_hom',f.app_eq_appLE,q.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE,Scheme.Hom.appLE_comp_appLE]
  congr 1
  exact H.w.symm
lemma natural {V W:U.Opens} (i:W⟶V):
    X.presheaf.map (homOfLE (f.preimage_mono (j.image_mono i.le))).op≫(ringIso q k j f H W).hom=
      (ringIso q k j f H V).hom≫P.presheaf.map (homOfLE (q.preimage_mono i.le)).op:=by
  simp only [ringIso_hom,Scheme.Hom.map_appLE,Scheme.Hom.appLE_map]
/-- Actual O_U-module base-change isomorphism for an open cartesian square.
Both directions use the original open-immersion section isomorphisms. -/
@[expose] def iso:(PushforwardStructureSheaf318.object f).restrict j≅
    PushforwardStructureSheaf318.object q:=by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun W=>?_) ?_
  · refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙forget₂ RingCat AddCommGrpCat).mapIso
        (ringIso q k j f H W.unop)) ?_
    intro a
    ext s
    change (q.app W.unop a)*(ringIso q k j f H W.unop).hom s=
      (ringIso q k j f H W.unop).hom (f.app (j ''ᵁW.unop) ((j.appIso W.unop).inv a)*(show Γ(X,f⁻¹ᵁ(j ''ᵁW.unop)) from s))
    rw [map_mul]
    congr 1
    have h:=congrArg (fun g:Γ(Y,j ''ᵁW.unop)⟶Γ(P,q⁻¹ᵁW.unop)=>g ((j.appIso W.unop).inv a))
      (scalar_square q k j f H W.unop)
    simpa only [CommRingCat.comp_apply,CommRingCat.hom_inv_apply] using h.symm
  · intro W V g
    ext s
    exact congrArg (fun h:Γ(X,f⁻¹ᵁ(j ''ᵁW.unop))⟶Γ(P,q⁻¹ᵁV.unop)=>h s)
      (natural q k j f H g.unop)
lemma iso_component (W:U.Opens) (s:Γ((PushforwardStructureSheaf318.object f).restrict j,W)):
    (iso q k j f H).hom.app W s=(ringIso q k j f H W).hom s:=rfl
lemma iso_hom_inv:(iso q k j f H).hom≫(iso q k j f H).inv=𝟙 _ :=(iso q k j f H).hom_inv_id
lemma iso_inv_hom:(iso q k j f H).inv≫(iso q k j f H).hom=𝟙 _ :=(iso q k j f H).inv_hom_id
end OpenPullbackStructure318
