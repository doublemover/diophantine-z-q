module
public import SelectedComplexGenericRatFunc318
public import SelectedActualComplexOrdinaryScalar318
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public section
noncomputable section
open Polynomial
open SelectedComplexOrdinaryOneField318
open SelectedComplexGenericRatFunc318 SelectedActualComplexOrdinaryScalar318

namespace SelectedRationalGenericFromComplex318

abbrev QJ := RatFunc ℚ

@[expose] def rationalPolynomial : ℤ[X] →+* QJ :=
  (algebraMap ℚ[X] QJ).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem rationalPolynomial_injective : Function.Injective rationalPolynomial :=
  (IsFractionRing.injective ℚ[X] QJ).comp
    (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)

private theorem denominator_ne (N : ℕ) [NeZero N] :
    OpenJModel318.denominator N ≠ 0 := by
  unfold OpenJModel318.denominator
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (NeZero.ne N))
    · exact Polynomial.X_ne_zero
  · simpa using Polynomial.X_sub_C_ne_zero (1728 : ℤ)

/-- The entire rational generic coefficient field is based on the
original inverted polynomial, with literal J, not a selected root. -/
@[expose] def rationalGenericMap (N : ℕ) [NeZero N] : OpenJModel318.Base N →+* QJ :=
  IsLocalization.Away.lift (OpenJModel318.denominator N)
    (isUnit_iff_ne_zero.mpr (by
      intro h
      apply denominator_ne N
      apply rationalPolynomial_injective
      simpa only [map_zero] using h))

theorem rationalGenericMap_j (N : ℕ) [NeZero N] :
    rationalGenericMap N (OpenJModel318.jCoord N) = (RatFunc.X : QJ) := by
  rw [OpenJModel318.jCoord,rationalGenericMap,IsLocalization.Away.lift_eq]
  simp [rationalPolynomial,RatFunc.algebraMap_X]

@[expose] def changePolynomial : ℚ[X] →+* RatFunc ℂ :=
  (algebraMap ℂ[X] (RatFunc ℂ)).comp (Polynomial.mapRingHom (algebraMap ℚ ℂ))

theorem changePolynomial_injective : Function.Injective changePolynomial :=
  (IsFractionRing.injective ℂ[X] (RatFunc ℂ)).comp
    (Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective)

@[expose] def rationalToComplexRatFunc : QJ →+* RatFunc ℂ :=
  IsFractionRing.lift changePolynomial_injective

theorem rationalToComplexRatFunc_j :
    rationalToComplexRatFunc (RatFunc.X : QJ) = (RatFunc.X : RatFunc ℂ) := by
  rw [← RatFunc.algebraMap_X,rationalToComplexRatFunc,IsFractionRing.lift_algebraMap]
  simp [changePolynomial,RatFunc.algebraMap_X]

@[expose] def rationalToComplexGeneric : QJ →+* Generic :=
  ratEquiv.symm.toRingHom.comp rationalToComplexRatFunc

theorem rationalToComplexGeneric_j :
    rationalToComplexGeneric (RatFunc.X : QJ) =
      algebraMap SelectedComplexOrdinaryBase318.Base Generic
        SelectedComplexOrdinaryBase318.jCoord := by
  apply ratEquiv.injective
  change ratEquiv (ratEquiv.symm (rationalToComplexRatFunc (RatFunc.X : QJ))) = _
  rw [AlgEquiv.apply_symm_apply,rationalToComplexRatFunc_j,ratEquiv_literal_j,RatFunc.algebraMap_X]

/-- The ℚ(J) and ℂ(J) coefficient embeddings commute on the WHOLE
original localized ring, not merely on a set of sampled values. -/
theorem same_composite (N : ℕ) [NeZero N] :
    rationalToComplexGeneric.comp (rationalGenericMap N) =
      (algebraMap SelectedComplexOrdinaryBase318.Base Generic).comp (toComplex N) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator N))
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · change rationalToComplexGeneric (rationalGenericMap N (OpenJModel318.jCoord N)) =
      algebraMap SelectedComplexOrdinaryBase318.Base Generic (toComplex N (OpenJModel318.jCoord N))
    rw [rationalGenericMap_j,rationalToComplexGeneric_j,toComplex_j]

/-- A field of the whole mapped complex root algebra forces a field
of the whole mapped rational root algebra, with the same monic p.
This is primitive polynomial descent through an injective field map. -/
theorem rational_isField (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hp : p.Monic)
    (hC : IsField (AdjoinRoot (p.map
      ((algebraMap SelectedComplexOrdinaryBase318.Base Generic).comp (toComplex N))))) :
    IsField (AdjoinRoot (p.map (rationalGenericMap N))) := by
  letI : IsDomain SelectedComplexOrdinaryBase318.Base := coefficient_domain
  have hC' := AdjoinRoot.isField_iff_irreducible.mp hC
  have hi : Function.Injective rationalToComplexGeneric := rationalToComplexGeneric.injective
  apply AdjoinRoot.isField_iff_irreducible.mpr
  apply (hp.map _).isPrimitive.irreducible_of_irreducible_map_of_injective hi
  rwa [Polynomial.map_map,same_composite]

end SelectedRationalGenericFromComplex318

#print axioms SelectedRationalGenericFromComplex318.same_composite
#print axioms SelectedRationalGenericFromComplex318.rational_isField
