module
public import RelativeSchemeIntersection318
public section
noncomputable section
namespace ContactProjectiveUniversalIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (a b : Chart)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "ba" => ContactQuotientUniversalOriginal318.structureMap c a n
local notation "bb" => ContactQuotientUniversalOriginal318.structureMap c b n
local notation "t" => ContactQuotientUniversalOverlap318.structureMap c a b n
local notation "f" => ContactQuotientUniversalOverlap318.left c a b n
local notation "g" => ContactQuotientUniversalOverlap318.right c a b n
local notation "q" => ContactQuotientUniversalOriginal318.into c a n
local notation "r" => ContactQuotientUniversalOriginal318.into c b n
local notation "qa" => ContactQuotientUniversalOverlap318.leftInto c a b n
local notation "qb" => ContactQuotientUniversalOverlap318.rightInto c a b n
local notation "e" => ContactQuotientUniversalOverlapIso318.iso c a b n
local notation "ua" => ContactProjectiveUniversalAmbient318.into c n a
local notation "ub" => ContactProjectiveUniversalAmbient318.into c n b
abbrev leftSource : pullback p t ⟶ ContactQuotientUniversalOriginal318.curve c a n :=
  RelativeSchemeCoefficient318.map p ba t f rfl
abbrev rightSource : pullback p t ⟶ ContactQuotientUniversalOriginal318.curve c b n :=
  RelativeSchemeCoefficient318.map p bb t g (ContactQuotientUniversalOverlap318.right_over c a b n)
lemma source_cartesian : IsPullback (leftSource c n a b) (rightSource c n a b) ua ub :=
  RelativeSchemeIntersection318.cartesian p (ContactProjectiveParameterStructure318.structureMap c n)
    ba bb t (ContactProjectiveQuotientParameter318.into c n a)
    (ContactProjectiveQuotientParameter318.into c n b) f g
    (ContactProjectiveParameterStructure318.into_structureMap c n a)
    (ContactProjectiveParameterStructure318.into_structureMap c n b) rfl
    (ContactQuotientUniversalOverlap318.right_over c a b n)
    (ContactProjectiveParameterIntersection318.cartesian c n a b)
abbrev family := ContactQuotientUniversalOverlap318.leftFamily c a b n
abbrev left : family c n a b ⟶ ContactProjectiveUniversalAmbient318.localFamily c n a :=
  OriginalClosedFamilyRestriction318.toFamily p ba f q
abbrev right : family c n a b ⟶ ContactProjectiveUniversalAmbient318.localFamily c n b :=
  e.hom ≫ OriginalClosedFamilyRestriction318.toFamily p bb g r
instance left_open : IsOpenImmersion (left c n a b) := inferInstance
instance right_open : IsOpenImmersion (right c n a b) := by unfold right; infer_instance
lemma left_square : left c n a b ≫ q=qa ≫ leftSource c n a b :=
  (OriginalClosedFamilyRestriction318.into_map p ba t f rfl q).symm
lemma right_cartesian : IsPullback (right c n a b) qa r (rightSource c n a b) := by
  have H := OriginalClosedFamilyRestriction318.cartesian p bb t g
    (ContactQuotientUniversalOverlap318.right_over c a b n) r
  apply H.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [right,Iso.symm_hom,Iso.refl_hom,Category.comp_id,Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom,Iso.refl_hom,Category.comp_id]
    rw [← ContactQuotientUniversalOverlapIso318.iso_source,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
/-- Genuine original source-chart restriction of the other universal
family, before identifying its total family intersection. -/
lemma restriction : IsPullback (right c n a b) (left c n a b ≫ q)
    (ContactProjectiveUniversalAmbient318.localInto c n b) ua := by
  rw [left_square]
  exact (right_cartesian c n a b).paste_vert (source_cartesian c n a b).flip
/-- The overlap family is the actual categorical intersection in the
GLOBAL ORIGINAL source product, not just an abstract isomorphic family. -/
lemma cartesian : IsPullback (left c n a b) (right c n a b)
    (ContactProjectiveUniversalAmbient318.localInto c n a)
    (ContactProjectiveUniversalAmbient318.localInto c n b) :=
  MonoFactorPullback318.square (left c n a b) (right c n a b) q ua
    (ContactProjectiveUniversalAmbient318.localInto c n b) (restriction c n a b)
end ContactProjectiveUniversalIntersection318
