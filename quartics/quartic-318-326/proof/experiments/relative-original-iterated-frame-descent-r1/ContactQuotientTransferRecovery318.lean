module
public import ContactQuotientTransferSupport318
public section
noncomputable section
namespace ContactQuotientTransferRecovery318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientChartTransfer318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (a b : Chart) (S : CommRingCat.{0}) [Algebra ℚ S]
  (n : ℕ) (I : Ideal c a S n) (h : Supported c a b S n I)
/-- Reclassifying the same WHOLE original family back in its first chart
recovers the literal full quotient ideal, not merely its support. -/
lemma inverse : transfer c b a S n (transfer c a b S n I h)
    (ContactQuotientTransferSupport318.reverse c a b S n I h)=I := by
  apply Subtype.ext
  apply AffineClosedQuotientExtraction318.ideal_unique (S ⊗[ℚ] ring c a) _ I.val
    (comparison c a b S n I h).symm
  apply (cancel_mono (into c a S)).mp
  change ((comparison c a b S n I h).inv ≫ quotientInto c a S n I) ≫ into c a S=_
  rw [Category.assoc]
  change (comparison c a b S n I h).inv ≫ projectiveInto c a S n I=_
  rw [inverse_projective,lift_into]
lemma self : transfer c a a S n I (ContactQuotientTransferSupport318.self c a S n I)=I := by
  apply Subtype.ext
  apply AffineClosedQuotientExtraction318.ideal_unique (S ⊗[ℚ] ring c a) _ I.val (Iso.refl _)
  apply (cancel_mono (into c a S)).mp
  simpa only [Iso.refl_hom,Category.id_comp] using
    (lift_into c a a S n I (ContactQuotientTransferSupport318.self c a S n I)).symm
end ContactQuotientTransferRecovery318
