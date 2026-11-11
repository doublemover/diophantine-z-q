module
public import ContactQuotientTransferRecovery318
public section
noncomputable section
namespace ContactQuotientTransferIsoInvariant318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientChartTransfer318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (a b d : Chart) (S : CommRingCat.{0}) [Algebra ℚ S]
  (n : ℕ) (I : Ideal c a S n) (J : Ideal c b S n)
  (e : family c a S n I ≅ family c b S n J)
  (he : e.hom ≫ projectiveInto c b S n J=projectiveInto c a S n I)
  (ha : Supported c a d S n I) (hb : Supported c b d S n J)
/-- The new source-chart quotient depends only on the ACTUAL original
closed family, preserving its original embedding, not its old chart. -/
lemma transfer_eq : transfer c a d S n I ha=transfer c b d S n J hb := by
  apply Subtype.ext
  apply AffineClosedQuotientExtraction318.ideal_unique (S ⊗[ℚ] ring c d) _
    (transfer c b d S n J hb).val (e ≪≫ comparison c b d S n J hb)
  apply (cancel_mono (into c d S)).mp
  change (((e ≪≫ comparison c b d S n J hb).hom ≫
    quotientInto c d S n (transfer c b d S n J hb)) ≫ into c d S)=_
  simp only [Iso.trans_hom,Category.assoc]
  change e.hom ≫ ((comparison c b d S n J hb).hom ≫
    projectiveInto c d S n (transfer c b d S n J hb))=lift c a d S n I ha ≫ into c d S
  rw [comparison_projective,he,lift_into]
end ContactQuotientTransferIsoInvariant318
