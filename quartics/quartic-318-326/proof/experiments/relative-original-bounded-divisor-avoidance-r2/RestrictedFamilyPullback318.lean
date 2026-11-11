module
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace RestrictedFamilyPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {E A W T : Scheme.{u}} (π : E ⟶ A) (w : W ⟶ A) (j : T ⟶ W)
  (g : T ⟶ A) (h : j ≫ w=g)

/-- Nested restriction and base change identify the SAME family over T;
the base projection is retained rather than inferred from points. -/
lemma square : IsPullback
    (pullback.fst (pullback.snd π w) j ≫ pullback.fst π w)
    (pullback.snd (pullback.snd π w) j) π g := by
  have hp := (IsPullback.of_hasPullback (pullback.snd π w) j).paste_horiz
    (IsPullback.of_hasPullback π w)
  simpa only [h] using hp
@[expose] def iso : pullback (pullback.snd π w) j ≅ pullback π g :=
  (square π w j g h).isoPullback
@[reassoc] lemma iso_projection : (iso π w j g h).hom ≫ pullback.snd π g=
    pullback.snd (pullback.snd π w) j :=
  (square π w j g h).isoPullback_hom_snd
@[reassoc] lemma inv_projection : (iso π w j g h).inv ≫ pullback.snd (pullback.snd π w) j=
    pullback.snd π g := by
  rw [← iso_projection π w j g h, Iso.inv_hom_id_assoc]
end RestrictedFamilyPullback318
