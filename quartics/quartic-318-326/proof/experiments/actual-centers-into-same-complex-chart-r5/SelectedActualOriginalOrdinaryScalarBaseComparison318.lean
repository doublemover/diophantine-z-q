module
public import SelectedActualComplexPolynomialOrdinaryBase318
public import SelectedOriginalRationalOrdinary318
public import SelectedActualComplexOrdinaryScalar318
import all SelectedActualComplexPolynomialOrdinaryBase318

public section
noncomputable section
open scoped TensorProduct Polynomial

namespace SelectedActualOriginalOrdinaryScalarBaseComparison318

abbrev RQ := SelectedOriginalRationalOrdinary318.Base
abbrev RC := SelectedComplexOrdinaryBase318.Base

private abbrev dQ := SelectedOriginalRationalOrdinary318.denominator
private abbrev dC := SelectedComplexOrdinaryBase318.denominator

private theorem mapped_denominator :
    Polynomial.map (algebraMap ℚ ℂ) dQ = dC := by
  change Polynomial.map (algebraMap ℚ ℂ) SelectedOriginalRationalOrdinary318.denominator =
    SelectedComplexOrdinaryBase318.denominator
  unfold SelectedOriginalRationalOrdinary318.denominator SelectedComplexOrdinaryBase318.denominator
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_ofNat]

private def awayEquiv {A : Type*} [CommRing A] {a b : A} (h : a = b) :
    Localization.Away a ≃+* Localization.Away b := by
  subst b
  exact RingEquiv.refl _

private theorem awayEquiv_algebraMap {A : Type*} [CommRing A] {a b : A} (h : a = b) (r : A) :
    awayEquiv h (algebraMap A (Localization.Away a) r) =
      algebraMap A (Localization.Away b) r := by
  subst b
  unfold awayEquiv
  rfl

/-- The actual localization of the old ordinary base, over the exact mapped
denominator, is the existing ordinary complex base. No base point is chosen. -/
def identifyMappedBase :
    SelectedActualComplexPolynomialOrdinaryBase318.complexPolynomialBase ℚ ℂ SelectedOriginalRationalOrdinary318.denominator ≃+* RC :=
  awayEquiv mapped_denominator

theorem identifyMappedBase_polynomial (r : ℂ[X]) :
    identifyMappedBase (algebraMap ℂ[X]
      (SelectedActualComplexPolynomialOrdinaryBase318.complexPolynomialBase ℚ ℂ SelectedOriginalRationalOrdinary318.denominator) r) =
      algebraMap ℂ[X] RC r := by
  unfold identifyMappedBase
  exact awayEquiv_algebraMap mapped_denominator r

def scalarBase : ℂ ⊗[ℚ] RQ ≃+* RC :=
  (SelectedActualComplexPolynomialOrdinaryBase318.scalarOrdinaryBase ℚ ℂ dQ).trans
    identifyMappedBase

def oldBaseToComplex : RQ →+* RC :=
  scalarBase.toRingHom.comp
    (Algebra.TensorProduct.includeRight : RQ →ₐ[ℚ] ℂ ⊗[ℚ] RQ).toRingHom

theorem oldBaseToComplex_polynomial (r : ℚ[X]) :
    oldBaseToComplex (algebraMap ℚ[X] RQ r) =
      algebraMap ℂ[X] RC (r.map (algebraMap ℚ ℂ)) := by
  change identifyMappedBase
    (SelectedActualComplexPolynomialOrdinaryBase318.scalarOrdinaryBase ℚ ℂ dQ
      ((1 : ℂ) ⊗ₜ[ℚ] algebraMap ℚ[X] RQ r)) = _
  rw [SelectedActualComplexPolynomialOrdinaryBase318.scalarOrdinaryBase_polynomial,
    identifyMappedBase_polynomial]

theorem oldBaseToComplex_j :
    oldBaseToComplex SelectedOriginalRationalOrdinary318.jCoord =
      SelectedComplexOrdinaryBase318.jCoord := by
  unfold SelectedOriginalRationalOrdinary318.jCoord SelectedComplexOrdinaryBase318.jCoord
  rw [oldBaseToComplex_polynomial, Polynomial.map_X]

/-- The two base ring homomorphisms agree on the WHOLE literal original
localized integral base, not just on a specialization at one J. -/
theorem whole_scalar_square (N : ℕ) [NeZero N] :
    oldBaseToComplex.comp (SelectedOriginalRationalOrdinary318.toRational N) =
      SelectedActualComplexOrdinaryScalar318.toComplex N := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator N))
  apply Polynomial.ringHom_ext
  · intro n
    simp
  · change oldBaseToComplex
      (SelectedOriginalRationalOrdinary318.toRational N (OpenJModel318.jCoord N)) =
      SelectedActualComplexOrdinaryScalar318.toComplex N (OpenJModel318.jCoord N)
    rw [SelectedOriginalRationalOrdinary318.toRational_j, oldBaseToComplex_j,
      SelectedActualComplexOrdinaryScalar318.toComplex_j]

end SelectedActualOriginalOrdinaryScalarBaseComparison318

#print axioms SelectedActualOriginalOrdinaryScalarBaseComparison318.whole_scalar_square
