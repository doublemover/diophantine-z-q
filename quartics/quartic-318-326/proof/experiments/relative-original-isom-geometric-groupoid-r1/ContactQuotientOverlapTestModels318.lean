module
public import ContactQuotientUniversalOverlap318
public section
noncomputable section
namespace ContactQuotientOverlapTestModels318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (a b : Chart) (n : ℕ)
local notation "t" => ContactQuotientUniversalOverlap318.structureMap c a b n
local notation "U" => RelativeAffineTestCover318.cover ℚ t
variable (i : U.I₀)
abbrev ring : CommRingCat.{0} := RelativeAffineTestCover318.ring ℚ t i
instance algebra : Algebra ℚ (ring c a b n i) := RelativeAffineTestCover318.algebra ℚ t i
@[expose] def point : Point c a b n (ring c a b n i) :=
  ⟨U.f i,RelativeAffineTestCover318.over ℚ t i⟩
abbrev supportedIdeal := ContactQuotientOverlapPointEquiv318.recover c a b n (ring c a b n i) (point c a b n i)
abbrev leftIdeal : Ideal c a (ring c a b n i) n := (supportedIdeal c a b n i).val
abbrev rightIdeal : Ideal c b (ring c a b n i) n :=
  ContactQuotientChartTransfer318.transfer c a b (ring c a b n i) n (leftIdeal c a b n i)
    (supportedIdeal c a b n i).property
lemma left_point : (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ContactQuotientChart318.ring c a)
    (Fin n) (ring c a b n i) (leftIdeal c a b n i)).val=
      U.f i ≫ ContactQuotientUniversalOverlap318.left c a b n := by
  exact congrArg Subtype.val ((VaryingProjectiveQuotientEquiv318.equivalence ℚ
    (ContactQuotientChart318.ring c a) (Fin n) (ring c a b n i)).apply_symm_apply
      (underlying c a b n (ring c a b n i) (point c a b n i)))
lemma right_point : (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ContactQuotientChart318.ring c b)
    (Fin n) (ring c a b n i) (rightIdeal c a b n i)).val=
      U.f i ≫ ContactQuotientUniversalOverlap318.right c a b n := by
  have h := congrArg Subtype.val (classify_underlying c b a n (ring c a b n i)
    (ContactQuotientOverlapEquiv318.equivalence c a b (ring c a b n i) n (supportedIdeal c a b n i)))
  change (ContactQuotientOverlapPointEquiv318.transition c a b n (ring c a b n i)
    (point c a b n i)).val ≫ (parameterOpen c b a n).ι=_ at h
  rw [← ContactQuotientOverlapSchemeIso318.evaluate,Category.assoc] at h
  exact h.symm
abbrev comparison : ContactQuotientChart318.family c a (ring c a b n i) n (leftIdeal c a b n i) ≅
    ContactQuotientChart318.family c b (ring c a b n i) n (rightIdeal c a b n i) :=
  ContactQuotientChartTransfer318.comparison c a b (ring c a b n i) n
    (leftIdeal c a b n i) (supportedIdeal c a b n i).property
@[reassoc] lemma comparison_source : (comparison c a b n i).hom ≫
    projectiveInto c b (ring c a b n i) n (rightIdeal c a b n i)=
      projectiveInto c a (ring c a b n i) n (leftIdeal c a b n i) :=
  ContactQuotientChartTransfer318.comparison_projective _ _ _ _ _ _ _
@[reassoc] lemma comparison_base : (comparison c a b n i).hom ≫
    projection c b (ring c a b n i) n (rightIdeal c a b n i)=
      projection c a (ring c a b n i) n (leftIdeal c a b n i) := by
  rw [← ContactAffineQuotientToProjective318.into_projection,← Category.assoc,comparison_source,
    ContactAffineQuotientToProjective318.into_projection]
end ContactQuotientOverlapTestModels318
