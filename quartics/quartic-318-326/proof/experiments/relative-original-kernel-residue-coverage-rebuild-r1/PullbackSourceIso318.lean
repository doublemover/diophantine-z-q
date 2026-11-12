module
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace PullbackSourceIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {A A' B X : Scheme.{u}} (f : A ⟶ B) (g : A' ⟶ B)
  (b : X ⟶ B) (e : A ≅ A') (he : e.hom ≫ g=f)
@[expose] def hom : pullback f b ⟶ pullback g b :=
  pullback.lift (pullback.fst f b ≫ e.hom) (pullback.snd f b) (by
    rw [Category.assoc,he,pullback.condition])
lemma inverse_base : e.inv ≫ f=g := by rw [←he,Iso.inv_hom_id_assoc]
@[expose] def inv : pullback g b ⟶ pullback f b :=
  pullback.lift (pullback.fst g b ≫ e.inv) (pullback.snd g b) (by
    rw [Category.assoc,inverse_base f g e he,pullback.condition])
@[reassoc] lemma hom_fst : hom f g b e he ≫ pullback.fst g b=pullback.fst f b ≫ e.hom :=
  pullback.lift_fst ..
@[reassoc] lemma hom_snd : hom f g b e he ≫ pullback.snd g b=pullback.snd f b := pullback.lift_snd ..
@[reassoc] lemma inv_fst : inv f g b e he ≫ pullback.fst f b=pullback.fst g b ≫ e.inv :=
  pullback.lift_fst ..
@[reassoc] lemma inv_snd : inv f g b e he ≫ pullback.snd f b=pullback.snd g b := pullback.lift_snd ..
/-- Change the SOURCE factor by an actual over-base isomorphism; both
inverse identities and the unchanged second projection are retained. -/
@[expose] def iso : pullback f b ≅ pullback g b where
  hom := hom f g b e he
  inv := inv f g b e he
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,inv_fst,hom_fst_assoc,Iso.hom_inv_id,Category.comp_id,Category.id_comp]
    · simp only [Category.assoc,inv_snd,hom_snd,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,hom_fst,inv_fst_assoc,Iso.inv_hom_id,Category.comp_id,Category.id_comp]
    · simp only [Category.assoc,hom_snd,inv_snd,Category.id_comp]

end PullbackSourceIso318
