module
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace PullbackBaseIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {E B T U : Scheme.{u}} (p : E ⟶ B) (j : U ⟶ B) (e : T ≅ U)

/-- Change the base of an actual pullback by a specified isomorphism.
Both projection equations are explicit, including the nonidentity base map. -/
@[expose] def hom : pullback p (e.hom ≫ j) ⟶ pullback p j :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.hom) (by
    rw [Category.assoc,pullback.condition])
@[expose] def inv : pullback p j ⟶ pullback p (e.hom ≫ j) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.inv) (by
    rw [Category.assoc,Iso.inv_hom_id_assoc,pullback.condition])
@[reassoc] lemma hom_fst : hom p j e ≫ pullback.fst p j=pullback.fst p (e.hom ≫ j) :=
  pullback.lift_fst ..
@[reassoc] lemma hom_snd : hom p j e ≫ pullback.snd p j=
    pullback.snd p (e.hom ≫ j) ≫ e.hom := pullback.lift_snd ..
@[reassoc] lemma inv_fst : inv p j e ≫ pullback.fst p (e.hom ≫ j)=pullback.fst p j :=
  pullback.lift_fst ..
@[reassoc] lemma inv_snd : inv p j e ≫ pullback.snd p (e.hom ≫ j)=
    pullback.snd p j ≫ e.inv := pullback.lift_snd ..
@[expose] def iso : pullback p (e.hom ≫ j) ≅ pullback p j where
  hom := hom p j e
  inv := inv p j e
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,inv_fst,hom_fst,Category.id_comp]
    · simp only [Category.assoc,inv_snd,hom_snd_assoc,Iso.hom_inv_id,Category.comp_id,Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc,hom_fst,inv_fst,Category.id_comp]
    · simp only [Category.assoc,hom_snd,inv_snd_assoc,Iso.inv_hom_id,Category.comp_id,Category.id_comp]
end PullbackBaseIso318
