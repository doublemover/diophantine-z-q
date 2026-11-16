module
public import OpenLineRestriction318
public section
noncomputable section
namespace AffineModuleSectionEquiv318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 650000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (M:X.Modules) (U:X.Opens) (hU:IsAffineOpen U)
lemma image_top:hU.fromSpec ''ᵁ ⊤=U:=by
  rw [Scheme.Hom.image_top_eq_opensRange,hU.opensRange_fromSpec]
@[expose] def ringTransport:Γ(X,hU.fromSpec ''ᵁ ⊤)≅Γ(X,U):=
  X.presheaf.mapIso (eqToIso (image_top U hU).symm).op
lemma ring_square:(ringTransport U hU).hom≫(Scheme.ΓSpecIso Γ(X,U)).inv=
    (hU.fromSpec.appIso ⊤).hom:=by
  rw [hU.fromSpec.appIso_hom,hU.fromSpec_app_of_le _ (image_top U hU).ge]
  simp only [ringTransport,Functor.mapIso_hom,Iso.op_hom]
  simp only [Category.assoc,←Functor.map_comp]
  congr 1
lemma ring_roundtrip:(Scheme.ΓSpecIso Γ(X,U)).inv≫(hU.fromSpec.appIso ⊤).inv≫
    (ringTransport U hU).hom=𝟙 _:=by
  apply (cancel_mono (Scheme.ΓSpecIso Γ(X,U)).inv).mp
  simp only [Category.assoc,ring_square,Iso.inv_hom_id,Category.comp_id,Category.id_comp]
@[expose] def addIso:Γ(M.restrict hU.fromSpec,⊤)≅Γ(M,U):=
  M.restrictAppIso hU.fromSpec ⊤ ≪≫
    M.presheaf.mapIso (eqToIso (image_top U hU).symm).op
/-- Exact original affine sections, including the original coefficient ring
and the actual fromSpec comparison, not an abstract isomorphic module. -/
@[expose] def equiv:moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)≃ₗ[Γ(X,U)]Γ(M,U) where
  toFun:=(addIso M U hU).hom
  invFun:=(addIso M U hU).inv
  left_inv s:=by exact congrArg (fun g=>g s) (addIso M U hU).hom_inv_id
  right_inv s:=by exact congrArg (fun g=>g s) (addIso M U hU).inv_hom_id
  map_add' s t:=(addIso M U hU).hom.hom.map_add s t
  map_smul' a s:=by
    let s':Γ(M.restrict hU.fromSpec,⊤):=s
    let a':Γ(Spec Γ(X,U),⊤):=(Scheme.ΓSpecIso Γ(X,U)).inv a
    let t:Γ(M,hU.fromSpec ''ᵁ ⊤):=(M.restrictAppIso hU.fromSpec ⊤).hom s'
    let j:op (hU.fromSpec ''ᵁ ⊤)⟶op U:=(eqToHom (image_top U hU).symm).op
    have hfirst:(show Γ(M.restrict hU.fromSpec,⊤) from a • s)=a' • s':=by
      change ((Spec Γ(X,U)).presheaf.map (𝟙 (op ⊤))) a' • s'=a' • s'
      exact congrArg (fun z:Γ(Spec Γ(X,U),⊤)=>z • s')
        (congrArg (fun g:Γ(Spec Γ(X,U),⊤)⟶Γ(Spec Γ(X,U),⊤)=>g a')
          ((Spec Γ(X,U)).presheaf.map_id (op ⊤)))
    have h1:(M.restrictAppIso hU.fromSpec ⊤).hom (a' • s')=
        (hU.fromSpec.appIso ⊤).inv a' • t:=
      Scheme.Modules.smul_restrictAppIso_hom_apply hU.fromSpec M ⊤ a' s'
    have h2:M.presheaf.map j ((hU.fromSpec.appIso ⊤).inv a' • t)=
        X.presheaf.map j ((hU.fromSpec.appIso ⊤).inv a') • M.presheaf.map j t:=
      M.val.map_smul j _ t
    have hr:X.presheaf.map j ((hU.fromSpec.appIso ⊤).inv a')=a:=
      congrArg (fun g:Γ(X,U)⟶Γ(X,U)=>g a) (ring_roundtrip U hU)
    exact (congrArg (fun z:Γ(M.restrict hU.fromSpec,⊤)=>
      M.presheaf.map j ((M.restrictAppIso hU.fromSpec ⊤).hom z)) hfirst).trans
        ((congrArg (fun z:Γ(M,hU.fromSpec ''ᵁ ⊤)=>M.presheaf.map j z) h1).trans
          (h2.trans (congrArg (fun z:Γ(X,U)=>z • M.presheaf.map j t) hr)))
end AffineModuleSectionEquiv318
