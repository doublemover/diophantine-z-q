module
public import OriginalTensorLineChartUntwist318
public import OpenLineFrameCoordinates318
public import LineFrameChartCoordinates318
public import OriginalRestrictionTopScalar318
public section
noncomputable section
namespace OriginalTensorUntwistOver318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} (L N : Line X) (U : X.Opens)
  (e : N.object.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- The SAME full-chart tensor untwisting map on the actual over-open
site. This gives compatible coordinates on every original ambient subopen,
not independent choices of vector-space identifications. -/
def iso : (LineSheafTensor318.line L N).object.over U ≅ L.object.over U :=
  (Scheme.Modules.overEquiv U).functor.preimageIso <|
    ((Scheme.Modules.overFunctorEquiv U).app (LineSheafTensor318.line L N).object) ≪≫
      OriginalTensorLineChartUntwist318.iso L N U e ≪≫
        ((Scheme.Modules.overFunctorEquiv U).app L.object).symm

lemma map_iso : (Scheme.Modules.overEquiv U).functor.map (iso L N U e).hom =
    ((Scheme.Modules.overFunctorEquiv U).app (LineSheafTensor318.line L N).object).hom ≫
      (OriginalTensorLineChartUntwist318.iso L N U e).hom ≫
        ((Scheme.Modules.overFunctorEquiv U).app L.object).inv := by
  change (Scheme.Modules.overEquiv U).functor.map
    ((Scheme.Modules.overEquiv U).functor.preimage _) = _
  rw [Functor.map_preimage] <;> rfl

/-- Actual section coordinates, linear over the unchanged section ring. -/
def sections (V : X.Opens) (h : V ≤ U) :
    Γ((LineSheafTensor318.line L N).object,V) ≃ₗ[Γ(X,V)] Γ(L.object,V) :=
  ((SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (op (Over.mk (homOfLE h)))).mapIso (iso L N U e)).toLinearEquiv

lemma natural {V W : X.Opens} (hV : V ≤ U) (hW : W ≤ V)
    (s : Γ((LineSheafTensor318.line L N).object,V)) :
    L.object.presheaf.map (homOfLE hW).op (sections L N U e V hV s) =
      sections L N U e W (hW.trans hV)
        ((LineSheafTensor318.line L N).object.presheaf.map (homOfLE hW).op s) := by
  let k : Over.mk (homOfLE (hW.trans hV)) ⟶ Over.mk (homOfLE hV) :=
    Over.homMk (homOfLE hW) (Subsingleton.elim _ _)
  exact (congrArg (fun g => g s) ((iso L N U e).hom.val.naturality k.op)).symm

/-- The original inverse chart coordinates also retain the literal
presheaf restrictions, which is needed to lift chart representatives. -/
lemma inverse_natural {V W : X.Opens} (hV : V ≤ U) (hW : W ≤ V)
    (s : Γ(L.object,V)) :
    (LineSheafTensor318.line L N).object.presheaf.map (homOfLE hW).op
      ((sections L N U e V hV).symm s) =
      (sections L N U e W (hW.trans hV)).symm
        (L.object.presheaf.map (homOfLE hW).op s) := by
  let k : Over.mk (homOfLE (hW.trans hV)) ⟶ Over.mk (homOfLE hV) :=
    Over.homMk (homOfLE hW) (Subsingleton.elim _ _)
  exact (congrArg (fun g => g s) ((iso L N U e).inv.val.naturality k.op)).symm

/-- On every genuine open of the original chart, these exact ambient
coordinates are the original tensor untwisting component. -/
lemma image_apply (V : U.toScheme.Opens)
    (s : Γ((LineSheafTensor318.line L N).object,U.ι ''ᵁ V)) :
    sections L N U e (U.ι ''ᵁ V)
      (by simpa using U.ι.image_le_opensRange V) s =
        (OriginalTensorLineChartUntwist318.iso L N U e).hom.app V s := by
  have h := congrArg (fun φ => φ.val.app (op V) s) (map_iso L N U e)
  exact h

/-- Exact pure-section normalization, on ALL original chart subopens. -/
lemma image_pure (V : U.toScheme.Opens)
    (m : Γ(L.object,U.ι ''ᵁ V)) (n : Γ(N.object,U.ι ''ᵁ V)) :
    sections L N U e (U.ι ''ᵁ V)
      (by simpa using U.ι.image_le_opensRange V)
      (IntrinsicTensorSheaf318.pure L.object N.object (U.ι ''ᵁ V) m n) =
      (e.hom.app V n) • m := by
  rw [image_apply]
  exact OriginalTensorLineChartUntwist318.pure L N U e V m n
/-- The same formula on EVERY ambient subopen, including non-affine ones.
The image/preimage equality is transported across a universally quantified
section formula, so no section is replaced by a chosen extension. -/
lemma pure (V : X.Opens) (hV : V ≤ U)
    (m : Γ(L.object,V)) (n : Γ(N.object,V)) :
    sections L N U e V hV (IntrinsicTensorSheaf318.pure L.object N.object V m n) =
      (OpenLineFrameCoordinates318.frame N.object U e.symm V hV).symm n • m := by
  have hp : ∀ (m' : Γ(L.object,U.ι ''ᵁ (U.ι ⁻¹ᵁ V)))
      (n' : Γ(N.object,U.ι ''ᵁ (U.ι ⁻¹ᵁ V))),
      sections L N U e (U.ι ''ᵁ (U.ι ⁻¹ᵁ V))
        (by simpa using U.ι.image_le_opensRange (U.ι ⁻¹ᵁ V))
        (IntrinsicTensorSheaf318.pure L.object N.object _ m' n') =
      (OpenLineFrameCoordinates318.frame N.object U e.symm _
        (by simpa using U.ι.image_le_opensRange (U.ι ⁻¹ᵁ V))).symm n' • m' := by
    intro m' n'
    rw [image_pure]
    congr 1
    exact (LineFrameChartCoordinates318.over_inv_app N.object U e.symm (U.ι ⁻¹ᵁ V) n').symm
  have hi : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]
  have hp' : ∀ (m' : Γ(L.object,V)) (n' : Γ(N.object,V)),
      sections L N U e V hV (IntrinsicTensorSheaf318.pure L.object N.object V m' n') =
        (OpenLineFrameCoordinates318.frame N.object U e.symm V hV).symm n' • m' := by
    simpa only [hi] using hp
  exact hp' m n
/-- Exact full-open comparison, with the ORIGINAL image-of-top transport
on both endpoints. This is not an identification of unnamed section types. -/
lemma top_square (s : Γ((LineSheafTensor318.line L N).object.restrict U.ι,⊤)) :
    sections L N U e U le_rfl
      (OriginalRestrictionTopScalar318.moduleTop (LineSheafTensor318.line L N).object U s) =
    OriginalRestrictionTopScalar318.moduleTop L.object U
      ((OriginalTensorLineChartUntwist318.iso L N U e).hom.app ⊤ s) := by
  let k : Over.mk (homOfLE (show U ≤ U from le_rfl)) ⟶
      Over.mk (homOfLE (show U.ι ''ᵁ ⊤ ≤ U from by simpa using U.ι.image_le_opensRange ⊤)) :=
    Over.homMk (eqToHom (LineFrameTopScalar318.image_top U).symm) (Subsingleton.elim _ _)
  have hn := congrArg (fun q => q s) ((iso L N U e).hom.val.naturality k.op)
  change sections L N U e U le_rfl
      (OriginalRestrictionTopScalar318.moduleTop (LineSheafTensor318.line L N).object U s) =
    OriginalRestrictionTopScalar318.moduleTop L.object U
      (sections L N U e (U.ι ''ᵁ ⊤) _ s) at hn
  rw [image_apply] at hn
  exact hn
end OriginalTensorUntwistOver318
