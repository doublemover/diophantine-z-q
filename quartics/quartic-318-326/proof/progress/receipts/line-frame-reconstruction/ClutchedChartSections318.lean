module
public import LineFrameChartCoordinates318
public import OpenClutchedLine318
public import CocycleTwistedCoordinates318
public section
noncomputable section
namespace ClutchedChartSections318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 550000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} (U V W:X.Opens)
lemma overlap_open:
    (U⊓V:X.Opens).ι ''ᵁ((OpenClutchedLine318.leftInclusion U V≫U.ι)⁻¹ᵁW)=(U⊓V)⊓W:=by
  rw [OpenClutchedLine318.leftInclusion,Scheme.homOfLE_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
@[expose] def overlapIso:
    Γ((U⊓V:X.Opens).toScheme,(OpenClutchedLine318.leftInclusion U V≫U.ι)⁻¹ᵁW)≅Γ(X,(U⊓V)⊓W):=
  X.presheaf.mapIso (eqToIso (overlap_open U V W).symm).op
lemma left_apply (s:Γ(U.toScheme,U.ι⁻¹ᵁW)):
    (overlapIso U V W).hom
      ((ClutchedModule318.restriction U.ι (OpenClutchedLine318.leftInclusion U V)).app W s)=
    X.presheaf.map (homOfLE (show (U⊓V)⊓W≤U⊓W from
      inf_le_inf inf_le_left le_rfl)).op
        ((LineFrameChartCoordinates318.ringIso U W).hom s):=by
  change (overlapIso U V W).hom
    ((OpenClutchedLine318.leftInclusion U V).app (U.ι⁻¹ᵁW) s)=_
  simp only [overlapIso,LineFrameChartCoordinates318.ringIso,Functor.mapIso_hom,
    OpenClutchedLine318.leftInclusion,Scheme.homOfLE_app]
  change ((X.presheaf.map _ ≫ X.presheaf.map _) : _⟶_) s=
    ((X.presheaf.map _ ≫ X.presheaf.map _) : _⟶_) s
  simp only [←Functor.map_comp]
  rfl
lemma right_apply (a:Γ(X,U⊓V)ˣ) (s:Γ(V.toScheme,V.ι⁻¹ᵁW)):
    (overlapIso U V W).hom
      ((ClutchedModule318.twistedRestriction U.ι V.ι
        (OpenClutchedLine318.leftInclusion U V) (OpenClutchedLine318.rightInclusion U V)
        (OpenClutchedLine318.square U V) (OpenClutchedLine318.transition U V a)).app W s)=
      X.presheaf.map (homOfLE (show (U⊓V)⊓W≤V⊓W from
        inf_le_inf inf_le_right le_rfl)).op
          ((LineFrameChartCoordinates318.ringIso V W).hom s) *
      X.presheaf.map (homOfLE (show (U⊓V)⊓W≤U⊓V from inf_le_left)).op a.val:=by
  rw [CocycleTwistedCoordinates318.twisted_app _ _ _ _ _ _ _
    (by rw [OpenClutchedLine318.square])]
  rw [map_mul]
  congr 1
  · simp only [overlapIso,LineFrameChartCoordinates318.ringIso,Functor.mapIso_hom,
      OpenClutchedLine318.rightInclusion,Scheme.homOfLE_app,
      Scheme.Opens.toScheme_presheaf_map]
    change ((X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) : _⟶_) s=
      ((X.presheaf.map _ ≫ X.presheaf.map _) : _⟶_) s
    simp only [←Functor.map_comp]
    rfl
  · simp only [overlapIso,Functor.mapIso_hom,
      OpenClutchedLine318.transition,Scheme.Opens.topIso_inv,
      Scheme.Opens.toScheme_presheaf_map]
    change ((X.presheaf.map _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) : _⟶_) a.val=_
    simp only [←Functor.map_comp]
    rfl
end ClutchedChartSections318
