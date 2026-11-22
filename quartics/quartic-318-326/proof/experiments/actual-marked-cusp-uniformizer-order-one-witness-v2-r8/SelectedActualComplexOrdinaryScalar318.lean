module
public import SelectedComplexOrdinaryBase318
public import OpenJComplexEvaluation318
public section
noncomputable section
open Polynomial
namespace SelectedActualComplexOrdinaryScalar318
open SelectedComplexOrdinaryBase318

@[expose] def integerPolynomialScalar : ℤ[X] →+* ℂ[X] :=
  Polynomial.mapRingHom (Int.castRingHom ℂ)

@[expose] def polynomialScalar : ℤ[X] →+* Base :=
  (algebraMap ℂ[X] Base).comp integerPolynomialScalar

theorem denominator_scalar (N : ℕ) [NeZero N] :
    IsUnit (polynomialScalar (OpenJModel318.denominator N)) := by
  have he : integerPolynomialScalar (OpenJModel318.denominator N) =
      (6*(N : ℂ[X]))*denominator := by
    simp [integerPolynomialScalar,OpenJModel318.denominator,denominator,mul_assoc]
  have hu₆ : IsUnit (6 : ℂ[X]) := by
    simpa only [map_ofNat] using
      ((isUnit_iff_ne_zero.mpr (by norm_num : (6 : ℂ) ≠ 0)).map (C : ℂ →+* ℂ[X]))
  have huN : IsUnit (N : ℂ[X]) := by
    have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    simpa only [map_natCast] using ((isUnit_iff_ne_zero.mpr hn).map (C : ℂ →+* ℂ[X]))
  change IsUnit (algebraMap ℂ[X] Base (integerPolynomialScalar (OpenJModel318.denominator N)))
  rw [he,map_mul]
  exact ((hu₆.mul huN).map (algebraMap ℂ[X] Base)).mul
    (IsLocalization.Away.algebraMap_isUnit (S := Base) denominator)

/-- The exact scalar arrow from the original literal open j-line:
the factor 6N is a unit over ℂ, not a new j-denominator. -/
@[expose] def toComplex (N : ℕ) [NeZero N] : OpenJModel318.Base N →+* Base :=
  IsLocalization.Away.lift (OpenJModel318.denominator N) (denominator_scalar N)

theorem toComplex_j (N : ℕ) [NeZero N] : toComplex N (OpenJModel318.jCoord N) = jCoord := by
  rw [OpenJModel318.jCoord,toComplex,IsLocalization.Away.lift_eq]
  simp [polynomialScalar,integerPolynomialScalar,jCoord]

/-- Specializing at an actual period gives exactly the original
literal evaluation, on the entire localized coefficient ring. -/
theorem evaluation_commutes (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    (h : OpenJComplexEvaluation318.Admissible τ) :
    (evaluation ⟨ActualQJ318.jInvariant τ,h⟩).comp (toComplex N) =
      OpenJComplexEvaluation318.evaluation N τ h := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator N))
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · change evaluation ⟨ActualQJ318.jInvariant τ,h⟩ (toComplex N (OpenJModel318.jCoord N)) =
      OpenJComplexEvaluation318.evaluation N τ h (OpenJModel318.jCoord N)
    rw [toComplex_j,evaluation_j,OpenJComplexEvaluation318.evaluation_jCoord]

end SelectedActualComplexOrdinaryScalar318

#print axioms SelectedActualComplexOrdinaryScalar318.toComplex_j
#print axioms SelectedActualComplexOrdinaryScalar318.evaluation_commutes
