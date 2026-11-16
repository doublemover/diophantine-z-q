module
public import ContactQuotientTriplePointEquiv318
public section
noncomputable section
namespace ContactQuotientTripleNaturality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientTripleData318 ContactQuotientTriplePointEquiv318
variable (c : Fin 4 → ℚˣ) (a b d : Chart) (n : ℕ)
  (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T] (φ : S →ₐ[ℚ] T)
abbrev testMap := RelativeAffineTestRule318.map ℚ (ContactQuotientTripleScheme318.structureMap c a b d n) S T φ
lemma first_map (x : ContactQuotientTripleScheme318.Test c a b d n S) :
    ContactQuotientTripleScheme318.firstPoint c a b d n T (testMap c a b d n S T φ x)=
      ContactQuotientOpenPointNaturality318.map c a b n S T φ
        (ContactQuotientTripleScheme318.firstPoint c a b d n S x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _
lemma second_map (x : ContactQuotientTripleScheme318.Test c a b d n S) :
    ContactQuotientTripleScheme318.secondPoint c a b d n T (testMap c a b d n S T φ x)=
      ContactQuotientOpenPointNaturality318.map c a d n S T φ
        (ContactQuotientTripleScheme318.secondPoint c a b d n S x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _
lemma test_ext (x y : ContactQuotientTripleScheme318.Test c a b d n S)
    (h₁ : ContactQuotientTripleScheme318.firstPoint c a b d n S x=
      ContactQuotientTripleScheme318.firstPoint c a b d n S y)
    (h₂ : ContactQuotientTripleScheme318.secondPoint c a b d n S x=
      ContactQuotientTripleScheme318.secondPoint c a b d n S y) : x=y := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact congrArg Subtype.val h₁
  · exact congrArg Subtype.val h₂
lemma classify_natural (x : Triple c a b d S n) :
    classify c a b d n T (ContactQuotientTripleData318.map c a b d S n T φ x)=
      testMap c a b d n S T φ (classify c a b d n S x) := by
  apply test_ext c a b d n T
  · rw [first_classify,first_map,first_classify]
    exact ContactQuotientOpenPointNaturality318.classify_natural c a b n S T φ (first c a b d S n x)
  · rw [second_classify,second_map,second_classify]
    exact ContactQuotientOpenPointNaturality318.classify_natural c a d n S T φ (second c a b d S n x)
lemma recover_natural (x : ContactQuotientTripleScheme318.Test c a b d n S) :
    recover c a b d n T (testMap c a b d n S T φ x)=
      ContactQuotientTripleData318.map c a b d S n T φ (recover c a b d n S x) := by
  apply (equivalence c a b d n T).injective
  change classify c a b d n T (recover c a b d n T (testMap c a b d n S T φ x))=
    classify c a b d n T (ContactQuotientTripleData318.map c a b d S n T φ (recover c a b d n S x))
  rw [classify_recover,classify_natural,classify_recover]
end ContactQuotientTripleNaturality318
