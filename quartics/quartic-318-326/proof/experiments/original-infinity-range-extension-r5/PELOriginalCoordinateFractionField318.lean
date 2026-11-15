module
public import PELOriginalCoordinateRangeDeck318
public import PELOriginalRegularEvaluationInjective318
public import FourRootActualGenericField318
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section
namespace PELOriginalCoordinateFractionField318
open AlgebraicGeometry CategoryTheory
open PELOriginalRegularCoordinateAlgebra318 PELOriginalCoordinateRangeDeck318
open PELOriginalCommonContactBase318 PELOriginalMaximalQuotient318

/-- The codomain is the literal original-function range. Surjectivity is
by that range definition; injectivity is the separately proved original
root-monomial extraction theorem, not assumed from model dimension. -/
@[expose] def coefficientMap : CoordinateRing →ₐ[ℂ] OriginalAlgebra where
  toFun a := ⟨evaluation a,⟨a,rfl⟩⟩
  map_zero' := Subtype.ext (map_zero evaluation)
  map_one' := Subtype.ext (map_one evaluation)
  map_add' a b := Subtype.ext (map_add evaluation a b)
  map_mul' a b := Subtype.ext (map_mul evaluation a b)
  commutes' c := Subtype.ext (evaluation.commutes c)
lemma coefficientMap_injective : Function.Injective coefficientMap := by
  intro a b h
  exact PELOriginalRegularEvaluationInjective318.evaluation_injective (congrArg Subtype.val h)
lemma coefficientMap_surjective : Function.Surjective coefficientMap := by
  rintro ⟨f,⟨a,ha⟩⟩
  exact ⟨a,Subtype.ext ha⟩
@[expose] def coordinateEquiv : CoordinateRing ≃ₐ[ℂ] OriginalAlgebra :=
  AlgEquiv.ofBijective coefficientMap ⟨coefficientMap_injective,coefficientMap_surjective⟩
lemma coordinateEquiv_value (a : CoordinateRing) (x : OriginalRegular) :
    (coordinateEquiv a).val x = evaluation a x := rfl

/-- Domain structure on the original function algebra is DERIVED through
its now-proved injective coordinate presentation. The whole ring is used,
not a selected component or an arbitrary replacement field. -/
instance originalDomain : IsDomain OriginalAlgebra := by
  letI : IsDomain CoordinateRing := FourRootActualGenericField318.affine_domain branches branches_injective
  exact Function.Injective.isDomain coordinateEquiv.symm coordinateEquiv.symm.injective

/-- Fraction field of the literal original coordinate-function algebra.
This is NOT asserted to be the entire original meromorphic function field,
nor a rational descent/canonical-model construction. -/
abbrev CoordinateFractionField := FractionRing OriginalAlgebra
@[expose] def fractionMap : CoordinateRing →+* CoordinateFractionField :=
  (algebraMap OriginalAlgebra CoordinateFractionField).comp coefficientMap.toRingHom
lemma fractionMap_injective : Function.Injective fractionMap :=
  (IsFractionRing.injective OriginalAlgebra CoordinateFractionField).comp coefficientMap_injective
lemma fractionMap_coefficient (a : CoordinateRing) :
    fractionMap a = algebraMap OriginalAlgebra CoordinateFractionField (coordinateEquiv a) := rfl

lemma coordinateEquiv_deck (w : Labels) (a : CoordinateRing) :
    coordinateEquiv (FourRootCoordinateRingSigns318.finiteEnd branches
      (OriginalContactInertiaBasis318.basis w) a) = deck w (coordinateEquiv a) := by
  apply Subtype.ext
  exact evaluation_deck w a

/-- The original range-algebra deck automorphism extends uniquely by the
native fraction-ring construction, retaining its exact coefficient map. -/
@[expose] def fieldDeck (w : Labels) : CoordinateFractionField ≃+* CoordinateFractionField :=
  IsFractionRing.ringEquivOfRingEquiv (deck w).toRingEquiv
lemma fieldDeck_coefficient (w : Labels) (a : OriginalAlgebra) :
    fieldDeck w (algebraMap OriginalAlgebra CoordinateFractionField a) =
      algebraMap OriginalAlgebra CoordinateFractionField (deck w a) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap (deck w).toRingEquiv a
lemma fieldDeck_original (w : Labels) (a : CoordinateRing) :
    fieldDeck w (fractionMap a) = fractionMap
      (FourRootCoordinateRingSigns318.finiteEnd branches (OriginalContactInertiaBasis318.basis w) a) := by
  rw [fractionMap_coefficient,fieldDeck_coefficient,←coordinateEquiv_deck,fractionMap_coefficient]
lemma fieldDeck_complex_scalar (w : Labels) (c : ℂ) :
    fieldDeck w (algebraMap OriginalAlgebra CoordinateFractionField (algebraMap ℂ OriginalAlgebra c)) =
      algebraMap OriginalAlgebra CoordinateFractionField (algebraMap ℂ OriginalAlgebra c) := by
  rw [fieldDeck_coefficient,(deck w).commutes]

/-- The affine isomorphism is a CONSEQUENCE of the original function-ring
presentation, not a definition substituting the model for the source. -/
@[expose] def affineIso : affine ≅ Spec (CommRingCat.of CoordinateRing) :=
  Scheme.Spec.mapIso coordinateEquiv.toRingEquiv.toCommRingCatIso.op
@[expose] def fractionMapScheme : Spec (CommRingCat.of CoordinateFractionField) ⟶ affine :=
  Spec.map (CommRingCat.ofHom (algebraMap OriginalAlgebra CoordinateFractionField))
@[expose] def fieldSpecDeck (w : Labels) :
    Spec (CommRingCat.of CoordinateFractionField) ≅ Spec (CommRingCat.of CoordinateFractionField) :=
  Scheme.Spec.mapIso (fieldDeck w).toCommRingCatIso.op

/-- Exact original-deck compatibility of the actual fraction-point map. -/
theorem fraction_deck_square (w : Labels) :
    (fieldSpecDeck w).hom ≫ fractionMapScheme = fractionMapScheme ≫ schemeDeck w := by
  change Spec.map (CommRingCat.ofHom (fieldDeck w).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap OriginalAlgebra CoordinateFractionField)) =
    Spec.map (CommRingCat.ofHom (algebraMap OriginalAlgebra CoordinateFractionField)) ≫
      Spec.map (CommRingCat.ofHom (deck w).toRingHom)
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact fieldDeck_coefficient w a
end PELOriginalCoordinateFractionField318
