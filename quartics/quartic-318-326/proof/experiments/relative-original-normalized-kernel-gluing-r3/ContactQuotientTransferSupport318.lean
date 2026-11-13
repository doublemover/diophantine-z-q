module
public import ContactQuotientChartTransfer318
public section
noncomputable section
namespace ContactQuotientTransferSupport318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientChartTransfer318
variable (c : Fin 4 → ℚˣ) (a b d : Chart) (S : CommRingCat.{0}) [Algebra ℚ S]
  (n : ℕ) (I : Ideal c a S n) (h : Supported c a b S n I)
lemma self : Supported c a a S n I := by
  rintro _ ⟨z,rfl⟩
  exact ⟨quotientInto c a S n I z,rfl⟩
/-- Whole-family support is preserved by the source-preserving quotient
comparison. This controls every third source chart on triple overlaps. -/
lemma forward (hd : Supported c a d S n I) :
    Supported c b d S n (transfer c a b S n I h) := by
  rintro _ ⟨z,rfl⟩
  have he := congrArg (fun f => f z) (inverse_projective c a b S n I h)
  change projectiveInto c a S n I ((comparison c a b S n I h).inv z)=_ at he
  rw [← he]
  exact hd ⟨_,rfl⟩
lemma backward (hd : Supported c b d S n (transfer c a b S n I h)) : Supported c a d S n I := by
  rintro _ ⟨z,rfl⟩
  have he := congrArg (fun f => f z) (comparison_projective c a b S n I h)
  change projectiveInto c b S n (transfer c a b S n I h) ((comparison c a b S n I h).hom z)=_ at he
  rw [← he]
  exact hd ⟨_,rfl⟩
lemma reverse : Supported c b a S n (transfer c a b S n I h) :=
  forward c a b a S n I h (self c a S n I)
lemma iff_supported : Supported c b d S n (transfer c a b S n I h) ↔ Supported c a d S n I :=
  ⟨backward c a b d S n I h,forward c a b d S n I h⟩
end ContactQuotientTransferSupport318
