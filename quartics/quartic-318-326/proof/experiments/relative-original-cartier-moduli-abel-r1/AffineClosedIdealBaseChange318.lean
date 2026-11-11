module
public import AffineClosedQuotientExtraction318
public import AffineQuotientPushout318
public section
noncomputable section
namespace AffineClosedIdealBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (B C : Type u) [CommRing B] [CommRing C] (φ : B →+* C)
variable {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B))
  (g : Y ⟶ Spec (CommRingCat.of C)) [IsClosedImmersion f] [IsClosedImmersion g]
  (k : Y ⟶ X) (h : IsPullback k g f (Spec.map (CommRingCat.ofHom φ)))
local notation "I" => AffineClosedQuotientExtraction318.ideal B f
local notation "J" => Ideal.map φ I
local notation "e" => AffineClosedQuotientExtraction318.comparison B f
/-- The intrinsic whole ideal of an actual base-changed affine closed
immersion is its literal extended ideal, for arbitrary ring maps. -/
lemma ideal_map : AffineClosedQuotientExtraction318.ideal C g=J := by
  have hs : IsPullback (k ≫ e.hom) g
      (AffineQuotientFactorRigidity318.into B I) (Spec.map (CommRingCat.ofHom φ)) := by
    apply h.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom,Category.id_comp]
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    · simpa only [Iso.refl_hom,Category.comp_id] using
        (AffineClosedQuotientExtraction318.comparison_into B f).symm
    · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
  let ht := (AffineQuotientPushout318.pullback (CommRingCat.ofHom φ) I J rfl).flip
  let d := hs.isoIsPullback _ _ ht
  apply AffineClosedQuotientExtraction318.ideal_unique C g J d
  exact hs.isoIsPullback_hom_snd ht
end AffineClosedIdealBaseChange318
