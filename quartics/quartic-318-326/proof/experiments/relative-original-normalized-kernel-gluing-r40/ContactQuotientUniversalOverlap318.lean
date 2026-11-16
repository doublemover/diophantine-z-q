module
public import ContactQuotientUniversalRestriction318
public section
noncomputable section
namespace ContactQuotientUniversalOverlap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ)
abbrev base := ContactQuotientOverlapSchemeRule318.scheme c a b n
abbrev structureMap := ContactQuotientOverlapSchemeRule318.structureMap c a b n
abbrev left : base c a b n ⟶ ContactQuotientUniversalOriginal318.parameter c a n := (parameterOpen c a b n).ι
abbrev right : base c a b n ⟶ ContactQuotientUniversalOriginal318.parameter c b n :=
  (ContactQuotientOverlapSchemeIso318.iso c a b n).hom ≫ (parameterOpen c b a n).ι
lemma right_over : right c a b n ≫ ContactQuotientUniversalOriginal318.structureMap c b n=structureMap c a b n := by
  rw [right,Category.assoc]
  exact ContactQuotientOverlapSchemeIso318.over c a b n
abbrev leftFamily := ContactQuotientUniversalRestriction318.family c a n (left c a b n)
abbrev rightFamily := ContactQuotientUniversalRestriction318.family c b n (right c a b n)
abbrev leftInto : leftFamily c a b n ⟶
    pullback (ContactIntrinsicDifferentials318.structureMap c) (structureMap c a b n) :=
  ContactQuotientUniversalRestriction318.into c a n (structureMap c a b n) (left c a b n) rfl
abbrev rightInto : rightFamily c a b n ⟶
    pullback (ContactIntrinsicDifferentials318.structureMap c) (structureMap c a b n) :=
  ContactQuotientUniversalRestriction318.into c b n (structureMap c a b n) (right c a b n) (right_over c a b n)
end ContactQuotientUniversalOverlap318
