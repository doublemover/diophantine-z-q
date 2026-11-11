module
public import ContactQuotientOverlapTestModels318
public section
noncomputable section
namespace ContactQuotientUniversalOverlapModels318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ)
local notation "t" => ContactQuotientUniversalOverlap318.structureMap c a b n
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "f" => ContactQuotientUniversalOverlap318.left c a b n
local notation "g" => ContactQuotientUniversalOverlap318.right c a b n
local notation "q" => ContactQuotientUniversalOverlap318.leftInto c a b n
local notation "r" => ContactQuotientUniversalOverlap318.rightInto c a b n
local notation "U" => RelativeAffineTestCover318.cover ℚ t
variable (i : U.I₀)
local notation "S" => ContactQuotientOverlapTestModels318.ring c a b n i
local notation "I" => ContactQuotientOverlapTestModels318.leftIdeal c a b n i
local notation "J" => ContactQuotientOverlapTestModels318.rightIdeal c a b n i
local notation "e" => ContactQuotientOverlapTestModels318.comparison c a b n i
abbrev leftMap : family c a S n I ⟶ ContactQuotientUniversalOverlap318.leftFamily c a b n :=
  ContactQuotientUniversalRestriction318.modelMap c a n f S (U.f i) I
    (ContactQuotientOverlapTestModels318.left_point c a b n i)
abbrev rightMap : family c a S n I ⟶ ContactQuotientUniversalOverlap318.rightFamily c a b n :=
  e.hom ≫ ContactQuotientUniversalRestriction318.modelMap c b n g S (U.f i) J
    (ContactQuotientOverlapTestModels318.right_point c a b n i)
lemma left_cartesian : IsPullback (leftMap c a b n i) (projection c a S n I)
    (q ≫ pullback.snd p t) (U.f i) := by
  rw [ContactQuotientUniversalRestriction318.into_base]
  exact ContactQuotientUniversalRestriction318.modelMap_cartesian c a n f S (U.f i) I
    (ContactQuotientOverlapTestModels318.left_point c a b n i)
lemma right_cartesian : IsPullback (rightMap c a b n i) (projection c a S n I)
    (r ≫ pullback.snd p t) (U.f i) := by
  rw [ContactQuotientUniversalRestriction318.into_base]
  have H := ContactQuotientUniversalRestriction318.modelMap_cartesian c b n g S (U.f i) J
    (ContactQuotientOverlapTestModels318.right_point c a b n i)
  apply H.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [rightMap,Iso.symm_hom,Iso.refl_hom,Category.comp_id,Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom,Iso.refl_hom,Category.comp_id]
    rw [← ContactQuotientOverlapTestModels318.comparison_base,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
lemma source : leftMap c a b n i ≫ q=rightMap c a b n i ≫ r := by
  rw [rightMap,Category.assoc]
  rw [ContactQuotientUniversalRestriction318.modelMap_source c a n t f rfl S (U.f i)
    (RelativeAffineTestCover318.over ℚ t i) I (ContactQuotientOverlapTestModels318.left_point c a b n i)]
  rw [ContactQuotientUniversalRestriction318.modelMap_source c b n t g
    (ContactQuotientUniversalOverlap318.right_over c a b n) S (U.f i)
    (RelativeAffineTestCover318.over ℚ t i) J (ContactQuotientOverlapTestModels318.right_point c a b n i)]
  rw [← Category.assoc,ContactQuotientOverlapTestModels318.comparison_source]
/-- The two actual original universal families on the true parameter
overlap have shared full local quotient models on EVERY affine base chart. -/
@[expose] def data : SchemeClosedFamilyLocalModels318.Data (pullback.snd p t) q r where
  family i := ContactQuotientChart318.family c a (ContactQuotientOverlapTestModels318.ring c a b n i) n
    (ContactQuotientOverlapTestModels318.leftIdeal c a b n i)
  projection i := ContactQuotientChart318.projection c a (ContactQuotientOverlapTestModels318.ring c a b n i) n
    (ContactQuotientOverlapTestModels318.leftIdeal c a b n i)
  left := leftMap c a b n
  right := rightMap c a b n
  left_cartesian := left_cartesian c a b n
  right_cartesian := right_cartesian c a b n
  over_source := source c a b n
end ContactQuotientUniversalOverlapModels318
