module
public import ContactProjectivePresentationIndependence318
public section
noncomputable section
namespace ContactProjectivePresentationIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveLocalPresentation318 ContactProjectiveGlobalClassifyingMap318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  {Z W : Scheme.{0}} (q : Z ⟶ ContactRelativeLinearOpenChart318.curve S c)
  (r : W ⟶ ContactRelativeLinearOpenChart318.curve S c) [IsClosedImmersion q] [IsClosedImmersion r]
  (e : Z ≅ W) (he : e.hom ≫ r=q) (D : Data c n S q)
/-- Transport through the actual whole-family source-preserving
isomorphism, retaining the same local full ideals and coefficient cover. -/
@[expose] def transport : Data c n S r where
  coefficients := D.coefficients
  chart := D.chart
  ideal := D.ideal
  toFamily i := D.toFamily i ≫ e.hom
  cartesian i := by
    apply (D.cartesian i).of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    · simp only [Iso.refl_hom,Category.id_comp]
    · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
    · simpa only [Iso.refl_hom,Category.comp_id] using he.symm
    · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
lemma transport_point : point c n S r (transport c n S q r e he D)=point c n S q D := by
  apply Subtype.ext
  apply Scheme.Cover.hom_ext (AffineCoefficientCover318.cover ℚ S D.coefficients) _ _
  intro i
  exact (local_classify c n S r (transport c n S q r e he D) i).trans
    (local_classify c n S q D i).symm
/-- Every presentation of any isomorphic original closed model gives
the same global parameter point, not just the transported presentation. -/
lemma invariant (E : Data c n S r) : point c n S q D=point c n S r E :=
  (transport_point c n S q r e he D).symm.trans
    (ContactProjectivePresentationIndependence318.independent c n S r (transport c n S q r e he D) E)
end ContactProjectivePresentationIso318
