module
public import ContactProjectiveParameterPoint318
public section
noncomputable section
namespace ContactProjectiveChartAgreement318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientChartTransfer318 ContactQuotientOverlapOpen318
open scoped TensorProduct
variable (c : Fin 4 → ℚˣ) (a b : Chart) (S : CommRingCat.{0}) [Algebra ℚ S]
  (n : ℕ) (I : Ideal c a S n) (J : Ideal c b S n)
  (e : family c a S n I ≅ family c b S n J)
  (he : e.hom ≫ projectiveInto c b S n J=projectiveInto c a S n I)
lemma supported : Supported c a b S n I := by
  rintro _ ⟨z,rfl⟩
  rw [← he]
  exact ⟨quotientInto c b S n J (e.hom z),rfl⟩
lemma transfer_eq : transfer c a b S n I (supported c a b S n I J e he)=J := by
  apply Subtype.ext
  apply AffineClosedQuotientExtraction318.ideal_unique (S ⊗[ℚ] ring c b) _ J.val e
  apply (cancel_mono (into c b S)).mp
  change (e.hom ≫ quotientInto c b S n J) ≫ into c b S=_
  rw [Category.assoc]
  change e.hom ≫ projectiveInto c b S n J=_
  rw [he,lift_into]
/-- Source-preserving isomorphic WHOLE original quotient families have
the SAME point in the actual glued projective parameter. -/
lemma agreement : ContactProjectiveParameterPoint318.ofIdeal c n S a I=
    ContactProjectiveParameterPoint318.ofIdeal c n S b J := by
  let h := supported c a b S n I J e he
  let x := ContactQuotientOverlapOpen318.classify c a b n S ⟨I,h⟩
  let y := ContactQuotientOverlapPointEquiv318.transition c a b n S x
  have hx : x.val ≫ (parameterOpen c a b n).ι=
      (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S I).val :=
    congrArg Subtype.val (classify_underlying c a b n S ⟨I,h⟩)
  have hy : y.val ≫ (parameterOpen c b a n).ι=
      (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c b) (Fin n) S J).val := by
    change (underlying c b a n S (ContactQuotientOverlapOpen318.classify c b a n S
      (ContactQuotientOverlapEquiv318.equivalence c a b S n
        (ContactQuotientOverlapPointEquiv318.recover c a b n S x)))).val=_
    rw [ContactQuotientOverlapPointEquiv318.recover_classify,classify_underlying]
    change (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c b) (Fin n) S (transfer c a b S n I h)).val=_
    rw [transfer_eq c a b S n I J e he]
  apply Subtype.ext
  change (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S I).val ≫ _=_
  rw [← hx,Category.assoc,← ContactProjectiveQuotientParameter318.glue_condition,
    ← Category.assoc,ContactQuotientOverlapSchemeIso318.evaluate]
  rw [← Category.assoc]
  change (y.val ≫ (parameterOpen c b a n).ι) ≫ ContactProjectiveQuotientParameter318.into c n b=_
  rw [hy]
end ContactProjectiveChartAgreement318
