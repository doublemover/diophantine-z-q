module
public import ContactQuotientTripleScheme318
public section
noncomputable section
namespace ContactQuotientTriplePointEquiv318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientTripleData318
open ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (a b d : Chart) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
local notation "E" => VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S
@[expose] def classify (x : Triple c a b d S n) : ContactQuotientTripleScheme318.Test c a b d n S := by
  let y := ContactQuotientOverlapOpen318.classify c a b n S (first c a b d S n x)
  let z := ContactQuotientOverlapOpen318.classify c a d n S (second c a b d S n x)
  have h : y.val ≫ (parameterOpen c a b n).ι=z.val ≫ (parameterOpen c a d n).ι :=
    congrArg Subtype.val ((classify_underlying c a b n S (first c a b d S n x)).trans
      (classify_underlying c a d n S (second c a b d S n x)).symm)
  refine ⟨pullback.lift y.val z.val h,?_⟩
  change pullback.lift y.val z.val h ≫ (pullback.fst _ _ ≫ _)=_
  rw [← Category.assoc,pullback.lift_fst]
  exact y.property
lemma first_classify (x : Triple c a b d S n) :
    ContactQuotientTripleScheme318.firstPoint c a b d n S (classify c a b d n S x)=
      ContactQuotientOverlapOpen318.classify c a b n S (first c a b d S n x) := by
  apply Subtype.ext
  exact pullback.lift_fst _ _ _
lemma second_classify (x : Triple c a b d S n) :
    ContactQuotientTripleScheme318.secondPoint c a b d n S (classify c a b d n S x)=
      ContactQuotientOverlapOpen318.classify c a d n S (second c a b d S n x) := by
  apply Subtype.ext
  exact pullback.lift_snd _ _ _
lemma recovered_equal (x : ContactQuotientTripleScheme318.Test c a b d n S) :
    (ContactQuotientOverlapPointEquiv318.recover c a b n S
      (ContactQuotientTripleScheme318.firstPoint c a b d n S x)).val=
    (ContactQuotientOverlapPointEquiv318.recover c a d n S
      (ContactQuotientTripleScheme318.secondPoint c a b d n S x)).val :=
  congrArg E.symm (ContactQuotientTripleScheme318.underlying_eq c a b d n S x)
@[expose] def recover (x : ContactQuotientTripleScheme318.Test c a b d n S) : Triple c a b d S n := by
  let I := ContactQuotientOverlapPointEquiv318.recover c a b n S
    (ContactQuotientTripleScheme318.firstPoint c a b d n S x)
  refine ⟨I.val,I.property,?_⟩
  rw [show I.val=(ContactQuotientOverlapPointEquiv318.recover c a d n S
    (ContactQuotientTripleScheme318.secondPoint c a b d n S x)).val from recovered_equal c a b d n S x]
  exact (ContactQuotientOverlapPointEquiv318.recover c a d n S
    (ContactQuotientTripleScheme318.secondPoint c a b d n S x)).property
lemma first_recover (x : ContactQuotientTripleScheme318.Test c a b d n S) :
    first c a b d S n (recover c a b d n S x)=ContactQuotientOverlapPointEquiv318.recover c a b n S
      (ContactQuotientTripleScheme318.firstPoint c a b d n S x) := rfl
lemma second_recover (x : ContactQuotientTripleScheme318.Test c a b d n S) :
    second c a b d S n (recover c a b d n S x)=ContactQuotientOverlapPointEquiv318.recover c a d n S
      (ContactQuotientTripleScheme318.secondPoint c a b d n S x) :=
  Subtype.ext (recovered_equal c a b d n S x)
lemma recover_classify (x : Triple c a b d S n) : recover c a b d n S (classify c a b d n S x)=x := by
  apply Subtype.ext
  change (ContactQuotientOverlapPointEquiv318.recover c a b n S
    (ContactQuotientTripleScheme318.firstPoint c a b d n S (classify c a b d n S x))).val=x.val
  simpa only [first_classify] using congrArg Subtype.val
    (ContactQuotientOverlapPointEquiv318.recover_classify c a b n S (first c a b d S n x))
lemma classify_recover (x : ContactQuotientTripleScheme318.Test c a b d n S) :
    classify c a b d n S (recover c a b d n S x)=x := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact congrArg Subtype.val ((first_classify c a b d n S (recover c a b d n S x)).trans
      ((congrArg (ContactQuotientOverlapOpen318.classify c a b n S) (first_recover c a b d n S x)).trans
        (ContactQuotientOverlapPointEquiv318.classify_recover c a b n S _)))
  · exact congrArg Subtype.val ((second_classify c a b d n S (recover c a b d n S x)).trans
      ((congrArg (ContactQuotientOverlapOpen318.classify c a d n S) (second_recover c a b d n S x)).trans
        (ContactQuotientOverlapPointEquiv318.classify_recover c a d n S _)))
/-- Exact representation of the three-supported full-quotient data by
the ACTUAL categorical intersection of the two parameter opens. -/
@[expose] def equivalence : Triple c a b d S n ≃ ContactQuotientTripleScheme318.Test c a b d n S where
  toFun := classify c a b d n S
  invFun := recover c a b d n S
  left_inv := recover_classify c a b d n S
  right_inv := classify_recover c a b d n S
end ContactQuotientTriplePointEquiv318
