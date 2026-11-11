module
public import OriginalClosedFamilyRestriction318
public section
noncomputable section
namespace ContactQuotientUniversalRestriction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (a : Chart) (n : ℕ) {T : Scheme.{0}}
  (t : T ⟶ Spec (CommRingCat.of ℚ)) (f : T ⟶ ContactQuotientUniversalOriginal318.parameter c a n)
  (hf : f ≫ ContactQuotientUniversalOriginal318.structureMap c a n=t)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "b" => ContactQuotientUniversalOriginal318.structureMap c a n
local notation "q" => ContactQuotientUniversalOriginal318.into c a n
abbrev family := OriginalClosedFamilyRestriction318.family p b f q
abbrev projection := OriginalClosedFamilyRestriction318.projection p b f q
abbrev into : family c a n f ⟶ pullback p t := OriginalClosedFamilyRestriction318.into p b t f hf q
instance closed : IsClosedImmersion (into c a n t f hf) := inferInstance
@[reassoc] lemma into_base : into c a n t f hf ≫ pullback.snd p t=projection c a n f :=
  OriginalClosedFamilyRestriction318.into_base _ _ _ _ _ _
variable (S : CommRingCat.{0}) [Algebra ℚ S] (x : Spec S ⟶ T)
  (hx : x ≫ t=VaryingSourceCoefficientPullback318.base ℚ S)
  (I : Ideal c a S n)
  (hI : (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) S I).val=x ≫ f)
lemma model_cartesian : IsPullback (ContactQuotientUniversalTest318.toFamily c a n S I)
    (ContactQuotientChart318.projection c a S n I) (q ≫ pullback.snd p b) (x ≫ f) := by
  rw [ContactQuotientUniversalOriginal318.into_base,← hI]
  exact VaryingProjectiveQuotientFamily318.cartesian ℚ (ring c a) (Fin n) S I
@[expose] def modelMap : ContactQuotientChart318.family c a S n I ⟶ family c a n f :=
  OriginalClosedFamilyRestriction318.lift p b f q x (ContactQuotientChart318.projection c a S n I)
    (ContactQuotientUniversalTest318.toFamily c a n S I) (model_cartesian c a n f S x I hI)
lemma modelMap_cartesian : IsPullback (modelMap c a n f S x I hI)
    (ContactQuotientChart318.projection c a S n I) (projection c a n f) x :=
  OriginalClosedFamilyRestriction318.lift_cartesian _ _ _ _ _ _ _ _
/-- Exact original-source equation for the actual local full ideal,
including its complete nonreduced quotient structure. -/
lemma modelMap_source : modelMap c a n f S x I hI ≫ into c a n t f hf=
    projectiveInto c a S n I ≫ RelativeSchemeCoefficient318.map p t
      (VaryingSourceCoefficientPullback318.base ℚ S) x hx := by
  apply pullback.hom_ext
  · rw [Category.assoc,OriginalClosedFamilyRestriction318.into_original,← Category.assoc,
      OriginalClosedFamilyRestriction318.lift_fst,Category.assoc,
      ContactQuotientUniversalOriginal318.into_original,← Category.assoc,
      ContactQuotientUniversalTest318.toFamily_original,Category.assoc,Category.assoc,
      RelativeSchemeCoefficient318.map_fst,ContactQuotientUniversalTest318.literal_original]
  · rw [Category.assoc,into_base]
    change OriginalClosedFamilyRestriction318.lift p b f q x _ _ _ ≫
      OriginalClosedFamilyRestriction318.projection p b f q=_
    rw [OriginalClosedFamilyRestriction318.lift_snd,Category.assoc,RelativeSchemeCoefficient318.map_snd,
      ← Category.assoc,ContactAffineQuotientToProjective318.into_projection]
end ContactQuotientUniversalRestriction318
