module
public import OpenChartModuleImages318
public section
noncomputable section
namespace OpenSheafRestrictionCompatibility318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenSheafTransition318 OpenChartModuleImages318
set_option maxHeartbeats 1800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A B : X.Modules} {U V : X.Opens}

/-- Original restriction composition along an actual inclusion of opens. -/
@[expose] def path (M : X.Modules) (h : V ≤ U) :
    M.restrict V.ι ≅ (M.restrict U.ι).restrict (X.homOfLE h) :=
  (Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M

/-- Actual open-subscheme restriction of an original ambient sheaf iso,
normalized by the original composition/equality comparisons at both ends. -/
@[expose] def schemeRestrict (e : A.restrict U.ι ≅ B.restrict U.ι) (h : V ≤ U) :
    A.restrict V.ι ≅ B.restrict V.ι :=
  path A h ≪≫ (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫ (path B h).symm

lemma image_eq (h : V ≤ U) (W : V.toScheme.Opens) :
    U.ι ''ᵁ ((X.homOfLE h) ''ᵁ W) = V.ι ''ᵁ W := by
  simpa only [Scheme.homOfLE_ι] using (Scheme.Hom.comp_image (X.homOfLE h) U.ι W).symm

lemma map_toOver_hom (e : A.restrict U.ι ≅ B.restrict U.ι) :
    (Scheme.Modules.overEquiv U).functor.map (toOverIso U e).hom =
      ((Scheme.Modules.overFunctorEquiv U).app A).hom ≫ e.hom ≫
        ((Scheme.Modules.overFunctorEquiv U).app B).inv := by
  change (Scheme.Modules.overEquiv U).functor.map
    ((Scheme.Modules.overEquiv U).functor.preimage
      (((Scheme.Modules.overFunctorEquiv U).app A) ≪≫ e ≪≫
        ((Scheme.Modules.overFunctorEquiv U).app B).symm).hom) = _
  rw [Functor.map_preimage]
  rfl

lemma toOver_hom_app (e : A.restrict U.ι ≅ B.restrict U.ι)
    (W : U.toScheme.Opens) (s : Γ(A,U.ι ''ᵁ W)) :
    (toOverIso U e).hom.val.app
      (op (Over.mk (homOfLE (show U.ι ''ᵁ W ≤ U from by
        simpa using U.ι.image_le_opensRange W)))) s = e.hom.app W s := by
  exact congrArg (fun f => f.app W s) (map_toOver_hom e)

lemma schemeRestrict_hom_app (e : A.restrict U.ι ≅ B.restrict U.ι) (h : V ≤ U)
    (W : V.toScheme.Opens) (s : Γ(A,V.ι ''ᵁ W)) :
    (schemeRestrict e h).hom.app W s =
      B.presheaf.map (homOfLE (image_eq h W).symm.le).op
        (e.hom.app ((X.homOfLE h) ''ᵁ W)
          (A.presheaf.map (homOfLE (image_eq h W).le).op s)) := by
  simp only [schemeRestrict, path, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Functor.mapIso_hom]
  change B.presheaf.map _ (B.presheaf.map _
    (e.hom.app ((X.homOfLE h) ''ᵁ W)
      (A.presheaf.map _ (A.presheaf.map _ s)))) = _
  rw [← A.presheaf.map_comp_apply, ← B.presheaf.map_comp_apply]
  rfl

/-- The actual scheme restriction and canonical over-open restriction
agree under the original equivalence, including both original endpoint maps. -/
lemma restriction_compatible (e : A.restrict U.ι ≅ B.restrict U.ι) (h : V ≤ U) :
    toOverIso V (schemeRestrict e h) = restrictIso (toOverIso U e) h := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv V).functor.map_injective
  rw [map_toOver_hom]
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  let I₁ := U.ι ''ᵁ ((X.homOfLE h) ''ᵁ W)
  let I₂ := V.ι ''ᵁ W
  have h₁ : I₁ ≤ U := by simpa [I₁] using U.ι.image_le_opensRange ((X.homOfLE h) ''ᵁ W)
  have h₂ : I₂ ≤ U := (show V.ι ''ᵁ W ≤ V from by simpa using V.ι.image_le_opensRange W).trans h
  let q : Over.mk (homOfLE h₂) ⟶ Over.mk (homOfLE h₁) :=
    Over.homMk (homOfLE (image_eq h W).symm.le)
  have hn := PresheafOfModules.naturality_apply (toOverIso U e).hom.val q.op
    (A.presheaf.map (homOfLE (image_eq h W).le).op s)
  change (toOverIso U e).hom.val.app (op (Over.mk (homOfLE h₂)))
      (A.presheaf.map (homOfLE (image_eq h W).symm.le).op
        (A.presheaf.map (homOfLE (image_eq h W).le).op s)) =
    B.presheaf.map (homOfLE (image_eq h W).symm.le).op
      ((toOverIso U e).hom.val.app (op (Over.mk (homOfLE h₁)))
        (A.presheaf.map (homOfLE (image_eq h W).le).op s)) at hn
  simp only [← A.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, homOfLE_refl,
    op_id, Functor.map_id, ConcreteCategory.id_apply] at hn
  rw [toOver_hom_app] at hn
  change (schemeRestrict e h).hom.app W s =
    (toOverIso U e).hom.val.app (op (Over.mk (homOfLE h₂))) s
  rw [schemeRestrict_hom_app]
  exact hn.symm
end OpenSheafRestrictionCompatibility318
