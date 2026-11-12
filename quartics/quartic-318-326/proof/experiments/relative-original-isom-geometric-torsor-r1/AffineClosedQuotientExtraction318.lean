module
public import AffineQuotientFactorRigidity318
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public section
noncomputable section
namespace AffineClosedQuotientExtraction318
open AlgebraicGeometry CategoryTheory
universe u
variable (B : Type u) [CommRing B] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsClosedImmersion f]
/-- The genuine full ideal of a closed immersion into the original affine
source, extracted from the affine closed-immersion theorem. -/
@[expose] def ideal : Ideal B := Classical.choose (IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion f))
@[expose] def comparison : X ≅ Spec (CommRingCat.of (B ⧸ ideal B f)) :=
  Classical.choose (Classical.choose_spec (IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion f)))
@[reassoc] lemma comparison_into : (comparison B f).hom ≫
    AffineQuotientFactorRigidity318.into B (ideal B f)=f :=
  (Classical.choose_spec (Classical.choose_spec
    (IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion f)))).symm
@[reassoc] lemma comparison_inv_into : (comparison B f).inv ≫ f=
    AffineQuotientFactorRigidity318.into B (ideal B f) := by
  rw [← comparison_into,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
/-- Extraction is independent of the quotient model chosen by Spec_iff. -/
lemma ideal_unique (J : Ideal B) (e : X ≅ Spec (CommRingCat.of (B ⧸ J)))
    (h : e.hom ≫ AffineQuotientFactorRigidity318.into B J=f) : ideal B f=J := by
  apply le_antisymm
  · apply AffineQuotientFactorRigidity318.ideal_le B J (ideal B f)
      (e.inv ≫ (comparison B f).hom)
    rw [Category.assoc,comparison_into,← h,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  · apply AffineQuotientFactorRigidity318.ideal_le B (ideal B f) J
      ((comparison B f).inv ≫ e.hom)
    rw [Category.assoc,h,comparison_inv_into]
end AffineClosedQuotientExtraction318
