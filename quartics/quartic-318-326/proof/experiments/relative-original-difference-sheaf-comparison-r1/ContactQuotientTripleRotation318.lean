module
public import ContactQuotientTripleNaturality318
public section
noncomputable section
namespace ContactQuotientTripleRotation318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318 ContactQuotientTripleData318 ContactQuotientTriplePointEquiv318
variable (c : Fin 4 → ℚˣ) (a b d : Chart) (n : ℕ)
@[expose] def rule : RelativeAffineTestRule318.Rule ℚ
    (ContactQuotientTripleScheme318.structureMap c a b d n)
    (ContactQuotientTripleScheme318.structureMap c b d a n) where
  app S _ x := classify c b d a n S (rotate c a b d S n (recover c a b d n S x))
  natural S T _ _ φ x := by
    change classify c b d a n T (rotate c a b d T n
      (recover c a b d n T (ContactQuotientTripleNaturality318.testMap c a b d n S T φ x)))=_
    rw [ContactQuotientTripleNaturality318.recover_natural,rotation_natural,
      ContactQuotientTripleNaturality318.classify_natural]
/-- Rotation is on the ACTUAL categorical triple intersection. -/
@[expose] def rotation : ContactQuotientTripleScheme318.scheme c a b d n ⟶
    ContactQuotientTripleScheme318.scheme c b d a n :=
  RelativeAffineTestGluing318.realize ℚ _ _ (rule c a b d n)
@[reassoc] lemma over : rotation c a b d n ≫ ContactQuotientTripleScheme318.structureMap c b d a n=
    ContactQuotientTripleScheme318.structureMap c a b d n := RelativeAffineTestGluing318.over ℚ _ _ _
@[reassoc] lemma evaluate (S : CommRingCat.{0}) [Algebra ℚ S]
    (x : ContactQuotientTripleScheme318.Test c a b d n S) :
    x.val ≫ rotation c a b d n=
      (classify c b d a n S (rotate c a b d S n (recover c a b d n S x))).val :=
  RelativeAffineTestEvaluation318.evaluate ℚ _ _ _ S x
lemma leg : rotation c a b d n ≫ ContactQuotientTripleScheme318.second c b d a n=
    ContactQuotientTripleScheme318.first c a b d n ≫ (ContactQuotientOverlapSchemeIso318.iso c a b n).hom := by
  apply RelativeAffineTestExt318.hom_ext ℚ (ContactQuotientTripleScheme318.structureMap c a b d n)
  intro S _ x
  rw [← Category.assoc,evaluate]
  change (ContactQuotientTripleScheme318.secondPoint c b d a n S
      (classify c b d a n S (rotate c a b d S n (recover c a b d n S x)))).val=_
  rw [second_classify,rotation_leg,first_recover]
  change (ContactQuotientOverlapPointEquiv318.transition c a b n S
    (ContactQuotientTripleScheme318.firstPoint c a b d n S x)).val=
      x.val ≫ (ContactQuotientTripleScheme318.first c a b d n ≫ (ContactQuotientOverlapSchemeIso318.iso c a b n).hom)
  rw [← Category.assoc]
  exact (ContactQuotientOverlapSchemeIso318.evaluate c a b n S
    (ContactQuotientTripleScheme318.firstPoint c a b d n S x)).symm
lemma cycle : rotation c a b d n ≫ rotation c b d a n ≫ rotation c d a b n=𝟙 _ := by
  apply RelativeAffineTestExt318.hom_ext ℚ (ContactQuotientTripleScheme318.structureMap c a b d n)
  intro S _ x
  rw [← Category.assoc,evaluate,← Category.assoc,evaluate,recover_classify,evaluate,recover_classify,
    rotation_cycle,classify_recover,Category.comp_id]
end ContactQuotientTripleRotation318
