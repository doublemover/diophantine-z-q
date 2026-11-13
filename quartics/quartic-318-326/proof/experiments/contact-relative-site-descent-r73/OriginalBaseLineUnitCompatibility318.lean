module
public import CanonicalLocalMapCompatibility318
public section
noncomputable section
namespace OriginalBaseLineUnitCompatibility318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineOriginalCoverComparison318 AffineOriginalReconstructionSquare318
set_option maxHeartbeats 2800000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
  (L : Line Y)
abbrev datum := OriginalCanonicalDescent318.datum f L
abbrev reconstructed := AffineMorphismGlobalLine318.line f (datum f L)

lemma comparison_nested (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    (Scheme.Modules.pullback (Y.homOfLE h)).map (OriginalBaseLineOpenUnit318.comparison f L U).hom ≫
      (PullbackPathComposition318.iso (Y.homOfLE h) U.1.ι V.1.ι (Scheme.homOfLE_ι Y h)).hom.app L.object =
    (PullbackPathComposition318.iso (Y.homOfLE h) U.1.ι V.1.ι (Scheme.homOfLE_ι Y h)).hom.app
      (reconstructed f L).object ≫ (OriginalBaseLineOpenUnit318.comparison f L V).hom := by
  letI : IsAffineHom (f ∣_ V.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V.1).flip (inferInstance : IsAffineHom f)
  letI : Flat (f ∣_ V.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V.1).flip (inferInstance : Flat f)
  letI : Surjective (f ∣_ V.1) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f V.1).flip (inferInstance : Surjective f)
  apply GlobalAffineLineFaithfulness318.pullback_injective (f ∣_ V.1)
    (L:=LineSheafPullback318.line (Y.homOfLE h) (LineSheafPullback318.line U.1.ι (reconstructed f L)))
    (K:=LineSheafPullback318.line V.1.ι L)
  exact CanonicalLocalMapCompatibility318.after_cover f (f ∣_ U.1) (f ∣_ V.1)
    (sourceOpen f U).ι U.1.ι (morphismRestrict_ι f U.1).symm
    (sourceInclusion f U V h) (Y.homOfLE h) (open_square f U V h)
    (sourceOpen f V).ι V.1.ι (morphismRestrict_ι f V.1).symm
    (Scheme.homOfLE_ι X (f.preimage_mono h)) (Scheme.homOfLE_ι Y h)
    (reconstructed f L).object L.object (AffineMorphismGlobalRecovery318.comparison f (datum f L)).hom
    (OriginalBaseLineOpenUnit318.comparison f L U).hom (OriginalBaseLineOpenUnit318.comparison f L V).hom
    (OriginalBaseLineOpenUnit318.comparison_cover f L U) (OriginalBaseLineOpenUnit318.comparison_cover f L V)

@[expose] def restriction (U : Y.affineOpens) :
    (reconstructed f L).object.restrict U.1.ι ≅ L.object.restrict U.1.ι :=
  PullbackRestrictionCompatibility318.restriction (OriginalBaseLineOpenUnit318.comparison f L U)

lemma restriction_nested (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    OpenSheafRestrictionCompatibility318.schemeRestrict (restriction f L U) h = restriction f L V :=
  PullbackRestrictionCompatibility318.compatible h
    (OriginalBaseLineOpenUnit318.comparison f L U) (OriginalBaseLineOpenUnit318.comparison f L V)
    (comparison_nested f L U V h)

@[expose] def overIso (U : Y.affineOpens) : (reconstructed f L).object.over U.1 ≅ L.object.over U.1 :=
  OpenChartModuleImages318.toOverIso U.1 (restriction f L U)

lemma overIso_nested (U V : Y.affineOpens) (h : V.1 ≤ U.1) :
    OpenSheafTransition318.restrictIso (overIso f L U) h = overIso f L V := by
  rw [overIso,← OpenSheafRestrictionCompatibility318.restriction_compatible,restriction_nested]
end OriginalBaseLineUnitCompatibility318
