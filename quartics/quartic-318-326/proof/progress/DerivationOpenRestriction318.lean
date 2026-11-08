module
public import FamilyIntrinsicDifferentials318
public import IntrinsicUniversalComparison318
public section
noncomputable section
namespace DerivationOpenRestriction318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
  {R : CommRingCat.{u}} (φ : (Functor.const Y.Opensᵒᵖ).obj R ⟶ Y.presheaf)

/-- Restrict actual coefficients through the regular-function isomorphisms of
an open immersion. -/
@[expose] def coefficients : (Functor.const X.Opensᵒᵖ).obj R ⟶ X.presheaf where
  app U := φ.app (op (j ''ᵁ U.unop)) ≫ (j.appIso U.unop).hom
  naturality {U V} i := by
    dsimp
    rw [Category.id_comp,Category.assoc,←j.appIso_hom_naturality]
    rw [←Category.assoc,←φ.naturality]
    rfl

/-- Restriction of a genuine derivation to the actual restricted module sheaf. -/
@[expose] def restrict {M : Y.Modules}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val φ) :
    PresheafOfModulesOfCommRing.Derivation' (M.restrict j).val (coefficients j φ) where
  d {U} := (d.d (X:=op (j ''ᵁ U.unop))).comp
    (j.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul {U} a b := by
    change d.d ((j.appIso U.unop).inv (a*b)) = _
    rw [map_mul,d.d_mul]
    rfl
  d_map {U V} i a := by
    change d.d ((j.appIso V.unop).inv (X.presheaf.map i a)) =
      M.val.map (j.opensFunctor.op.map i) (d.d ((j.appIso U.unop).inv a))
    have h := congrArg (fun k => k a) (j.appIso_inv_naturality i)
    exact (congrArg (fun z => d.d (X:=op (j ''ᵁ V.unop)) z) h).trans
      (d.d_map (j.opensFunctor.op.map i) ((j.appIso U.unop).inv a))
  d_app {U} a := by
    change d.d ((j.appIso U.unop).inv ((j.appIso U.unop).hom (φ.app _ a)))=0
    rw [Iso.hom_inv_id_apply]
    exact d.d_app a

/-- Coefficients restrict along the actual open-immersion structure map. -/
theorem coefficients_app (U : Y.Opens) :
    φ.app (op U) ≫ j.app U =
      (coefficients j φ).app (op (j ⁻¹ᵁ U)) := by
  unfold coefficients
  apply (cancel_mono (j.appIso (j ⁻¹ᵁ U)).inv).1
  rw [Category.assoc,j.app_appIso_inv,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  exact (φ.naturality (homOfLE (j.image_preimage_le U)).op).symm

/-- A derivation on the open subscheme pushes to a genuine derivation into the
actual module pushforward. -/
@[expose] def push {M : X.Modules}
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (coefficients j φ)) :
    PresheafOfModulesOfCommRing.Derivation' ((Scheme.Modules.pushforward j).obj M).val φ where
  d {U} := (d.d (X:=op (j ⁻¹ᵁ U.unop))).comp (j.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change d.d (j.app U.unop (a*b)) = _
    rw [map_mul,d.d_mul]
    rfl
  d_map {U V} i a := by
    change d.d (j.app V.unop (Y.presheaf.map i a)) =
      M.val.map ((TopologicalSpace.Opens.map j.base).op.map i) (d.d (j.app U.unop a))
    have h := congrArg (fun k => k a) (j.naturality i)
    exact (congrArg (fun z => d.d (X:=op (j ⁻¹ᵁ V.unop)) z) h).trans
      (d.d_map ((TopologicalSpace.Opens.map j.base).op.map i) (j.app U.unop a))
  d_app {U} a := by
    change d.d (j.app U.unop (φ.app U a))=0
    have h := congrArg (fun k => k a) (coefficients_app j φ U.unop)
    exact (congrArg (fun z => d.d (X:=op (j ⁻¹ᵁ U.unop)) z) h).trans (d.d_app a)
end DerivationOpenRestriction318
