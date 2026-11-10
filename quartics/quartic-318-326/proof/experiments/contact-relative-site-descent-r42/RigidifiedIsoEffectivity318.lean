module
public import RigidifiedFaithfulDetection318
public section
noncomputable section
namespace RigidifiedIsoEffectivity318
open AlgebraicGeometry CategoryTheory LineSheafClass318 RelativeRigidifiedLine318
open RigidifiedLineIsomorphism318 RigidifiedOriginalDescentData318
open OriginalSchemeDescentBaseChangeMaps318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)
  [IsAffineHom f] [Flat f] [Surjective f]
  [IsAffineHom g] [Flat g] [Surjective g]
  {D E : Datum f g e e' square}
  (k : Hom D.underlying E.underlying)
  (a : CompatibleIso e' (localLine f g e e' square D) (localLine f g e e' square E))
  (hk : k.sheafHom = a.iso.hom)

@[expose] def inverseHom : Hom E.underlying D.underlying :=
  OriginalCanonicalDescent318.inverse f a.iso (by rw [← hk]; exact k.commutes)

/-- The existing original line-isomorphism descent, without replacing its
map or inverse, will also descend the section rigidification. -/
@[expose] def underlyingIso :
    (reconstructed f g e e' square D).object ≅ (reconstructed f g e e' square E).object :=
  AffineGlobalMorphismEffectivity318.iso f k (inverseHom f g e e' square k a hk)
    (by change k.sheafHom ≫ a.iso.inv = 𝟙 _; rw [hk]; exact a.iso.hom_inv_id)
    (by change a.iso.inv ≫ k.sheafHom = 𝟙 _; rw [hk]; exact a.iso.inv_hom_id)

lemma covering_square :
    (Scheme.Modules.pullback f).map (underlyingIso f g e e' square k a hk).hom ≫
        (RigidifiedEffectiveDescent318.comparison f g e e' square E).iso.hom =
      (RigidifiedEffectiveDescent318.comparison f g e e' square D).iso.hom ≫ a.iso.hom := by
  change (Scheme.Modules.pullback f).map (AffineGlobalMorphismEffectivity318.map f k) ≫
      (AffineMorphismGlobalRecovery318.comparison f E.underlying).hom =
    (AffineMorphismGlobalRecovery318.comparison f D.underlying).hom ≫ a.iso.hom
  rw [AffineGlobalMapCoverSquare318.cover_square,hk]

@[expose] def coveringCompatible : CompatibleIso e'
    (RigidifiedPointedPullback318.line e e' f g square
      (RigidifiedEffectiveDescent318.line f g e e' square D))
    (RigidifiedPointedPullback318.line e e' f g square
      (RigidifiedEffectiveDescent318.line f g e e' square E)) :=
  RigidifiedIsoCoherence318.compose e'
    (RigidifiedEffectiveDescent318.comparison f g e e' square D)
    (RigidifiedIsoCoherence318.compose e' a
      (RigidifiedIsoCoherence318.inverse e'
        (RigidifiedEffectiveDescent318.comparison f g e e' square E)))

lemma coveringCompatible_eq : (coveringCompatible f g e e' square a).iso =
    (Scheme.Modules.pullback f).mapIso (underlyingIso f g e e' square k a hk) := by
  apply Iso.ext
  apply (cancel_mono ((RigidifiedEffectiveDescent318.comparison f g e e' square E).iso.hom)).mp
  simpa only [coveringCompatible,RigidifiedIsoCoherence318.compose,
    RigidifiedIsoCoherence318.inverse,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    Category.assoc,Iso.inv_hom_id,Category.comp_id] using
      (covering_square f g e e' square k a hk).symm

/-- Every compatible local original isomorphism descends to a compatible
isomorphism of the actual reconstructed rigidified lines. -/
@[expose] def iso : CompatibleIso e
    (RigidifiedEffectiveDescent318.line f g e e' square D)
    (RigidifiedEffectiveDescent318.line f g e e' square E) :=
  RigidifiedFaithfulDetection318.descendCompatibility f g e e' square
    (underlyingIso f g e e' square k a hk) (coveringCompatible f g e e' square a)
    (coveringCompatible_eq f g e e' square k a hk)

lemma iso_cover :
    (Scheme.Modules.pullback f).map (iso f g e e' square k a hk).iso.hom ≫
        (RigidifiedEffectiveDescent318.comparison f g e e' square E).iso.hom =
      (RigidifiedEffectiveDescent318.comparison f g e e' square D).iso.hom ≫ a.iso.hom :=
  covering_square f g e e' square k a hk

lemma iso_unique (b : CompatibleIso e
    (RigidifiedEffectiveDescent318.line f g e e' square D)
    (RigidifiedEffectiveDescent318.line f g e e' square E))
    (hb : (Scheme.Modules.pullback f).map b.iso.hom ≫
        (RigidifiedEffectiveDescent318.comparison f g e e' square E).iso.hom =
      (RigidifiedEffectiveDescent318.comparison f g e e' square D).iso.hom ≫ a.iso.hom) :
    b = iso f g e e' square k a hk := by
  apply CompatibleIso.ext
  apply Iso.ext
  apply GlobalAffineLineFaithfulness318.pullback_injective f
  apply (cancel_mono ((RigidifiedEffectiveDescent318.comparison f g e e' square E).iso.hom)).mp
  exact hb.trans (iso_cover f g e e' square k a hk).symm
end RigidifiedIsoEffectivity318
