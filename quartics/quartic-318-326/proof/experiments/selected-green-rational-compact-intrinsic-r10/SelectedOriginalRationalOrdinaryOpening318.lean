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

private theorem ordinary_tower (hF : IsField (genericRoot N p)) :
    letI : Field (genericRoot N p) := hF.toField
    letI : Algebra ℚ[X] (genericRoot N p) := (polynomial (genericRoot N p) 1).toAlgebra
    @IsScalarTower ℚ[X] Base (genericRoot N p)
      (inferInstance : Algebra ℚ[X] Base).toSMul
      (inferInstance : Algebra Base (genericRoot N p)).toSMul
      (inferInstance : Algebra ℚ[X] (genericRoot N p)).toSMul := by
  letI : Field (genericRoot N p) := hF.toField
  letI : Algebra ℚ[X] (genericRoot N p) := (polynomial (genericRoot N p) 1).toAlgebra
  letI : IsScalarTower ℚ[X] Base QJ := rattower
  have h (a : ℚ[X]) : algebraMap ℚ[X] (genericRoot N p) a =
      algebraMap Base (genericRoot N p) (algebraMap ℚ[X] Base a) := by
    change algebraMap QJ (genericRoot N p) (basePolynomial 1 a) =
      algebraMap QJ (genericRoot N p) (algebraMap Base QJ (algebraMap ℚ[X] Base a))
    rw [← IsScalarTower.algebraMap_apply ℚ[X] Base QJ]
    simp [basePolynomial]
  exact IsScalarTower.of_algebraMap_eq h

/-- Actual inclusion of the two orders in their identical ambient field. -/
@[expose] def restrictOrdinary : CompactOrder N p hf →+* OrdinaryClosure N p := by
  letI : Field (genericRoot N p) := hf.toField
  letI : Algebra ℚ[X] (genericRoot N p) := (polynomial (genericRoot N p) 1).toAlgebra
  exact
    { toFun := fun x => ⟨(x : genericRoot N p),by
        letI := ordinary_tower N p hf
        exact x.property.tower_top⟩
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
  letI := ordinary_tower N p hf
  letI : Algebra (CompactOrder N p hf) (OrdinaryClosure N p) :=
    (restrictOrdinary N p hf).toAlgebra
  have hParam : (openParameter N p hf : genericRoot N p) =
      algebraMap ℚ[X] (genericRoot N p) denominator := rfl
  apply IsLocalization.Away.mk
  · have hs : algebraMap (CompactOrder N p hf) (OrdinaryClosure N p) (openParameter N p hf) =
        algebraMap Base (OrdinaryClosure N p) (algebraMap ℚ[X] Base denominator) := by
      apply Subtype.ext
      change ((restrictOrdinary N p hf (openParameter N p hf) : OrdinaryClosure N p) :
          genericRoot N p) =
        algebraMap Base (genericRoot N p) (algebraMap ℚ[X] Base denominator)
      rw [restrictOrdinary_value,hParam]
      exact IsScalarTower.algebraMap_apply ℚ[X] Base (genericRoot N p) denominator
    rw [hs]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Base) denominator).map
      (algebraMap Base (OrdinaryClosure N p))
  · intro z
    obtain ⟨⟨_,n,rfl⟩,hn⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (M := Submonoid.powers denominator) (Rₘ := Base) (z : genericRoot N p) z.property
    refine ⟨n,⟨(denominator ^ n : ℚ[X]) • (z : genericRoot N p),hn⟩,?_⟩
    apply Subtype.ext
    change (z : genericRoot N p) *
      (((restrictOrdinary N p hf (openParameter N p hf) : OrdinaryClosure N p) :
        genericRoot N p))^n =
      (denominator ^ n : ℚ[X]) • (z : genericRoot N p)
    rw [restrictOrdinary_value,hParam,Algebra.smul_def,map_pow,mul_comm]
  · intro x y h
    have hh : restrictOrdinary N p hf x = restrictOrdinary N p hf y := h
    have hv := congrArg (fun z : OrdinaryClosure N p => (z : genericRoot N p)) hh
    have hxy : x = y := Subtype.ext
      ((restrictOrdinary_value N p hf x).symm.trans (hv.trans (restrictOrdinary_value N p hf y)))
    exact ⟨0,by simpa only [pow_zero,one_mul] using hxy⟩

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
