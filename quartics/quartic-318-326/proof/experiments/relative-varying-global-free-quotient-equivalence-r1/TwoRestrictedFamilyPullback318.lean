module
public import RestrictedFamilyPullback318
public section
noncomputable section
namespace TwoRestrictedFamilyPullback318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {E A W B T : Scheme.{u}} (π : E ⟶ A) (w : W ⟶ A) (j : B ⟶ W)
  (l : T ⟶ B) (g : T ⟶ A) (h : l ≫ j ≫ w=g)

/-- Flatten two actual restrictions while retaining their final base
projection. Both isomorphisms come from the original Cartesian squares. -/
@[expose] def iso : pullback (pullback.snd (pullback.snd π w) j) l ≅ pullback π g :=
  RestrictedFamilyPullback318.iso (pullback.snd π w) j l (l ≫ j) rfl ≪≫
    RestrictedFamilyPullback318.iso π w (l ≫ j) g (by simpa only [Category.assoc] using h)
@[reassoc] lemma iso_projection : (iso π w j l g h).hom ≫ pullback.snd π g=
    pullback.snd (pullback.snd (pullback.snd π w) j) l := by
  rw [iso,Iso.trans_hom,Category.assoc,RestrictedFamilyPullback318.iso_projection,
    RestrictedFamilyPullback318.iso_projection]
@[reassoc] lemma inv_projection : (iso π w j l g h).inv ≫
    pullback.snd (pullback.snd (pullback.snd π w) j) l=pullback.snd π g := by
  rw [← iso_projection π w j l g h,Iso.inv_hom_id_assoc]
end TwoRestrictedFamilyPullback318
