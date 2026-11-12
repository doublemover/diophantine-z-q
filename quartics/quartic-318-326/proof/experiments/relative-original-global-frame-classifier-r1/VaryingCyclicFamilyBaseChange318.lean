module
public import VaryingCyclicIdealBaseChange318
public import VaryingQuotientCoefficientPullback318
public section
noncomputable section
namespace VaryingCyclicFamilyBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingSourceFreeQuotientClassifier318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (a : Cyclic R A ι S)
local notation "F" => toFramed R A ι S a
abbrev family : Scheme := CyclicQuotientFiniteFlat318.scheme F.action F.marked
abbrev into : family R A ι S a ⟶ Spec (CommRingCat.of (S ⊗[R] A)) :=
  CyclicQuotientFiniteFlat318.into F.action F.marked
abbrev projection : family R A ι S a ⟶ Spec (CommRingCat.of S) :=
  CyclicQuotientFiniteFlat318.projection F.action F.marked
@[reassoc] lemma into_projection : into R A ι S a ≫
    VaryingSourceCoefficientPullback318.projection R A S=projection R A ι S a := by
  rw [into,VaryingSourceCoefficientPullback318.projection,projection,
    CyclicQuotientFiniteFlat318.into,CyclicQuotientFiniteFlat318.projection,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq S (S ⊗[R] A)
    ((S ⊗[R] A) ⧸ ideal F.action F.marked)).symm
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
local notation "aT" => VaryingCyclicCoefficientSections318.mapCyclic R A ι S a T f
local notation "FT" => toFramed R A ι T aT
@[expose] def quotientMap : CommRingCat.of ((S ⊗[R] A) ⧸ ideal F.action F.marked) ⟶
    CommRingCat.of ((T ⊗[R] A) ⧸ ideal FT.action FT.marked) :=
  AffineQuotientPushout318.arrow
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom)
    _ _ (VaryingCyclicIdealBaseChange318.ideal_map R A ι S a T f)
abbrev map : family R A ι T aT ⟶ family R A ι S a := Spec.map (quotientMap R A ι S a T f)
lemma source_cartesian : IsPullback (into R A ι T aT) (map R A ι S a T f)
    (VaryingSourceCoefficientPullback318.sourceChange R A S T f) (into R A ι S a) :=
  AffineQuotientPushout318.pullback
    (CommRingCat.ofHom (VaryingNormalizedIdealBaseChange318.sourceMap R A S T f).toRingHom)
    _ _ (VaryingCyclicIdealBaseChange318.ideal_map R A ι S a T f)
/-- The actual original quotient family commutes with every coefficient
map, before choosing any word basis and without a flatness assumption. -/
lemma cartesian : IsPullback (map R A ι S a T f) (projection R A ι T aT)
    (projection R A ι S a) (VaryingSourceCoefficientPullback318.coefficientChange R S T f) := by
  have h := (source_cartesian R A ι S a T f).flip.paste_vert
    (VaryingSourceCoefficientPullback318.cartesian R A S T f)
  simpa only [into_projection] using h
end VaryingCyclicFamilyBaseChange318
