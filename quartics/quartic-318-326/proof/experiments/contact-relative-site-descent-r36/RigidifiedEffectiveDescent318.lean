module
public import RigidifiedOriginalDescentData318
public section
noncomputable section
namespace RigidifiedEffectiveDescent318
open AlgebraicGeometry CategoryTheory LineSheafClass318 RelativeRigidifiedLine318
open RigidifiedOriginalDescentData318 RigidifiedLineIsomorphism318
set_option maxHeartbeats 2400000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)
  [IsAffineHom f] [Flat f] [Surjective f]
  [IsAffineHom g] [Flat g] [Surjective g]
  (D : Datum f g e e' square)

/-- Descend the supplied trivialization itself, using the actual compatible
isomorphism between canonical data on the original base cover. -/
@[expose] def trivialization :
    (Scheme.Modules.pullback e).obj (reconstructed f g e e' square D).object ≅
      (LineSheafUnit318.line S).object :=
  OriginalGlobalLineMapDescent318.iso g (coveringIso f g e e' square D)
    (coveringHom f g e e' square D) (coveringHom_eq f g e e' square D)

lemma trivialization_cover :
    (Scheme.Modules.pullback g).mapIso (trivialization f g e e' square D) =
      coveringIso f g e e' square D :=
  OriginalGlobalLineMapDescent318.iso_cover g (coveringIso f g e e' square D)
    (coveringHom f g e e' square D) (coveringHom_eq f g e e' square D)

@[expose] def line : RigidifiedLine e where
  line := reconstructed f g e e' square D
  trivialization := trivialization f g e e' square D

/-- The unchanged original covering comparison respects the specified
local rigidification. No scalar correction or chosen class equality occurs. -/
@[expose] def comparison : CompatibleIso e'
    (RigidifiedPointedPullback318.line e e' f g square (line f g e e' square D))
    (localLine f g e e' square D) where
  iso := AffineMorphismGlobalEffectivity318.comparison f D.underlying
  commutes := by
    have h := congrArg Iso.hom (trivialization_cover f g e e' square D)
    simp only [Functor.mapIso_hom] at h
    change (Scheme.Modules.pullback e').map
        (AffineMorphismGlobalEffectivity318.comparison f D.underlying).hom ≫ D.trivialization.hom =
      (RigidifiedPointedPullback318.restrictionComparison e e' f g square).hom.app
          (reconstructed f g e e' square D).object ≫
        (Scheme.Modules.pullback g).map (trivialization f g e e' square D).hom ≫
          (IdentityCotangent318.pullbackUnitIso g).hom
    rw [pointedComparison_eq,h]
    simp only [coveringIso,Iso.trans_hom,Iso.symm_hom,Iso.app_inv,
      Functor.mapIso_hom,← Iso.app_hom,← Iso.app_inv,Category.assoc,
      Iso.hom_inv_id_assoc,Iso.inv_hom_id,Category.comp_id]

/-- Both the original line and its specified section trivialization are
effective for affine faithfully flat covering squares over arbitrary schemes. -/
theorem effective : ∃ L : RigidifiedLine e,
    Nonempty (CompatibleIso e' (RigidifiedPointedPullback318.line e e' f g square L)
      (localLine f g e e' square D)) :=
  ⟨line f g e e' square D,⟨comparison f g e e' square D⟩⟩

lemma trivialization_unique (t : (Scheme.Modules.pullback e).obj
    (reconstructed f g e e' square D).object ≅ (LineSheafUnit318.line S).object)
    (ht : (Scheme.Modules.pullback g).mapIso t = coveringIso f g e e' square D) :
    t = trivialization f g e e' square D := by
  apply Iso.ext
  apply GlobalAffineLineFaithfulness318.pullback_injective g
  exact congrArg Iso.hom (ht.trans (trivialization_cover f g e e' square D).symm)
end RigidifiedEffectiveDescent318
