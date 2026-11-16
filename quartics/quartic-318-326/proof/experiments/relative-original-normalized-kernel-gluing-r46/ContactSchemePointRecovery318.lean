module
public import ContactSchemePointTest318
public section
noncomputable section
namespace ContactSchemePointRecovery318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (f : ContactSchemePointFamily318.SchemePoint c n b)
/-- Extraction and classification recover EVERY actual global parameter
map on ANY coefficient scheme, proved on all affine tests. -/
lemma recover : ContactSchemeHilbertLocalRecovery318.point c n b (ContactSchemePointFamily318.extract c n b f)=f := by
  apply Subtype.ext
  apply RelativeAffineTestExt318.hom_ext ℚ b
  intro S _ x
  exact (ContactSchemeHilbertRule318.evaluate c n b (ContactSchemePointFamily318.extract c n b f) S x).trans
    (congrArg Subtype.val (ContactSchemePointTest318.classify_test c n b f S x))
end ContactSchemePointRecovery318
