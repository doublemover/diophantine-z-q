module
public import SelectedOriginalRationalOrdinaryIntegral318
public import SelectedOriginalGenericClosureOverlap318
public import Mathlib.RingTheory.Localization.Integral
public section
noncomputable section

open Polynomial
open SelectedOriginalRationalOrdinary318 SelectedOriginalRationalOrdinaryRoot318
open SelectedOriginalRationalOrdinaryIntegral318
open SelectedOriginalGenericChartClosures318
open SelectedRationalGenericFromComplex318
namespace SelectedOriginalRationalOrdinaryOpening318

attribute [local instance] SelectedOriginalRationalOrdinary318.ratscalar

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
variable (hf : IsField (genericRoot N p))

/-- The order on chart 1 of the projective normalization, with
algebra structure given by the literal polynomial map to J. -/
abbrev CompactOrder :=
  letI : Field (genericRoot N p) := hf.toField
  SelectedOriginalGenericClosureOverlap318.Order (genericRoot N p) 1

abbrev OrdinaryClosure := integralClosure Base (genericRoot N p)

@[expose] def openParameter : CompactOrder N p hf := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ[X] (genericRoot N p) := (polynomial (genericRoot N p) 1).toAlgebra
  exact algebraMap ℚ[X] (CompactOrder N p hf) denominator

private theorem ordinary_tower :
    letI : Field (genericRoot N p) := hf.toField
    letI : Algebra ℚ[X] (genericRoot N p) := (polynomial (genericRoot N p) 1).toAlgebra
    IsScalarTower ℚ[X] Base (genericRoot N p) := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ[X] (genericRoot N p) := (polynomial (genericRoot N p) 1).toAlgebra
  letI : IsScalarTower ℚ[X] Base QJ := rattower
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap QJ (genericRoot N p) (basePolynomial 1 a) =
    algebraMap QJ (genericRoot N p) (algebraMap Base QJ (algebraMap ℚ[X] Base a))
  rw [← IsScalarTower.algebraMap_apply ℚ[X] Base QJ]
  simp [basePolynomial]

/-- Actual inclusion of the two orders in their identical ambient field. -/
@[expose] def restrictOrdinary : CompactOrder N p hf →+* OrdinaryClosure N p := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ[X] (genericRoot N p) := (polynomial (genericRoot N p) 1).toAlgebra
  letI : IsScalarTower ℚ[X] Base (genericRoot N p) := by exact ordinary_tower N p hf
  exact
    { toFun := fun x => ⟨(x : genericRoot N p),x.property.tower_top⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }

theorem restrictOrdinary_value (x : CompactOrder N p hf) :
    (restrictOrdinary N p hf x : genericRoot N p) = (x : genericRoot N p) := rfl

/-- The ordinary open is exactly D(J(J-1728)) of the actual compact
chart order. In the ambient field the denominator is already a unit;
integral closure commutes with this exact localization. -/
theorem restrictOrdinary_isLocalization :
    letI : Algebra (CompactOrder N p hf) (OrdinaryClosure N p) :=
      (restrictOrdinary N p hf).toAlgebra
    IsLocalization.Away (openParameter N p hf) (OrdinaryClosure N p) := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ[X] (genericRoot N p) := (polynomial (genericRoot N p) 1).toAlgebra
  letI : IsScalarTower ℚ[X] Base (genericRoot N p) := ordinary_tower N p hf
  letI : Algebra (CompactOrder N p hf) (OrdinaryClosure N p) :=
    (restrictOrdinary N p hf).toAlgebra
  letI : Algebra ℚ[X] (OrdinaryClosure N p) :=
    ((algebraMap Base (OrdinaryClosure N p)).comp (algebraMap ℚ[X] Base)).toAlgebra
  letI : IsScalarTower ℚ[X] (CompactOrder N p hf) (OrdinaryClosure N p) :=
    IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext
      ((IsScalarTower.algebraMap_apply ℚ[X] Base (genericRoot N p) a).symm))
  letI : IsScalarTower (CompactOrder N p hf) (OrdinaryClosure N p) (genericRoot N p) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have huv : IsUnit (algebraMap ℚ[X] (genericRoot N p) denominator) := by
    rw [IsScalarTower.algebraMap_apply ℚ[X] Base (genericRoot N p)]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Base) denominator).map
      (algebraMap Base (genericRoot N p))
  letI : IsLocalization.Away (algebraMap ℚ[X] (genericRoot N p) denominator)
      (genericRoot N p) :=
    IsLocalization.away_of_isUnit_of_bijective _ huv Function.bijective_id
  exact IsLocalization.Away.integralClosure
    (S := genericRoot N p) (Rf := Base) (Sf := genericRoot N p) denominator

/-- Genuine algebra isomorphism to the same rational ordinary root ring
from the corresponding principal open of the whole compact chart. -/
def openingIso (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative)) :
    Localization.Away (openParameter N p hf) ≃+* ordinaryRoot N p := by
  letI : Algebra (CompactOrder N p hf) (OrdinaryClosure N p) :=
    (restrictOrdinary N p hf).toAlgebra
  letI : IsLocalization.Away (openParameter N p hf) (OrdinaryClosure N p) :=
    restrictOrdinary_isLocalization N p hf
  let e := IsLocalization.algEquiv (Submonoid.powers (openParameter N p hf))
    (Localization.Away (openParameter N p hf)) (OrdinaryClosure N p)
  exact e.toRingEquiv.trans (closureToOrdinary N p hp hd).toRingEquiv

theorem openingIso_order_value (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))
    (a : CompactOrder N p hf) :
    genericEmbedding N p (openingIso N p hf hp hd (algebraMap (CompactOrder N p hf)
      (Localization.Away (openParameter N p hf)) a)) = (a : genericRoot N p) := by
  letI : Algebra (CompactOrder N p hf) (OrdinaryClosure N p) :=
    (restrictOrdinary N p hf).toAlgebra
  letI : IsLocalization.Away (openParameter N p hf) (OrdinaryClosure N p) :=
    restrictOrdinary_isLocalization N p hf
  change genericEmbedding N p (closureToOrdinary N p hp hd
    (IsLocalization.algEquiv (Submonoid.powers (openParameter N p hf))
      (Localization.Away (openParameter N p hf)) (OrdinaryClosure N p)
      (algebraMap (CompactOrder N p hf) (Localization.Away (openParameter N p hf)) a))) = _
  rw [AlgEquiv.commutes,closureToOrdinary_value]
  exact restrictOrdinary_value N p hf a

end SelectedOriginalRationalOrdinaryOpening318

#print axioms SelectedOriginalRationalOrdinaryOpening318.restrictOrdinary_isLocalization
#print axioms SelectedOriginalRationalOrdinaryOpening318.openingIso_order_value
