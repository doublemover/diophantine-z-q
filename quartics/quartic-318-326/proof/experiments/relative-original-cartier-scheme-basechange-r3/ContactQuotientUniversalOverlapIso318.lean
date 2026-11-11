module
public import ContactQuotientUniversalOverlapModels318
public section
noncomputable section
namespace ContactQuotientUniversalOverlapIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ)
local notation "t" => ContactQuotientUniversalOverlap318.structureMap c a b n
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "q" => ContactQuotientUniversalOverlap318.leftInto c a b n
local notation "r" => ContactQuotientUniversalOverlap318.rightInto c a b n
/-- Genuine whole-family overlap isomorphism over the SAME original
projective source, constructed from all exact full-ideal affine tests. -/
@[expose] def iso : ContactQuotientUniversalOverlap318.leftFamily c a b n ≅
    ContactQuotientUniversalOverlap318.rightFamily c a b n :=
  SchemeClosedFamilyLocalModels318.iso (pullback.snd p t) q r
    (ContactQuotientUniversalOverlapModels318.data c a b n)
@[reassoc] lemma iso_source : (iso c a b n).hom ≫ r=q :=
  SchemeClosedFamilyLocalModels318.iso_into _ _ _ _
@[reassoc] lemma iso_base : (iso c a b n).hom ≫
    ContactQuotientUniversalRestriction318.projection c b n (ContactQuotientUniversalOverlap318.right c a b n)=
      ContactQuotientUniversalRestriction318.projection c a n (ContactQuotientUniversalOverlap318.left c a b n) := by
  rw [← ContactQuotientUniversalRestriction318.into_base,← Category.assoc,iso_source,
    ContactQuotientUniversalRestriction318.into_base]
/-- Full ideal-sheaf agreement, not radical or support agreement. -/
lemma ideal_eq : q.ker=r.ker := by
  rw [← iso_source]
  exact Scheme.Hom.ker_comp_of_isIso _ _
end ContactQuotientUniversalOverlapIso318
