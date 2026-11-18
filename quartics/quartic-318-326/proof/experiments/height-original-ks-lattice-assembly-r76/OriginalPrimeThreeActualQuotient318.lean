module
public import FourRootGenericReduced318
public import OriginalIntegerAffineModel318
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.Data.ZMod.QuotientRing
public section
noncomputable section
namespace OriginalPrimeThreeActualQuotient318
open Polynomial
open scoped TensorProduct
@[expose] def twist : Fin 4 → ℚˣ := fun _ => 1
abbrev Order := OriginalIntegerAffineModel318.Order twist
abbrev J : Ideal ℤ := Ideal.span {(3 : ℤ)}
abbrev I : Ideal ℤ[X] := J.map (C : ℤ →+* ℤ[X])
abbrev Q := ℤ[X] ⧸ I

@[expose] def coefficientRingEquiv : Q ≃+* (ZMod 3)[X] :=
  (Ideal.polynomialQuotientEquivQuotientPolynomial J).symm.trans
    (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod 3))

theorem coefficientRingEquiv_mk (p : ℤ[X]) :
    coefficientRingEquiv (Ideal.Quotient.mk I p) =
      p.map (Int.castRingHom (ZMod 3)) := by
  simp only [coefficientRingEquiv, RingEquiv.trans_apply,
    Ideal.polynomialQuotientEquivQuotientPolynomial_symm_mk,
    Polynomial.mapEquiv_apply, Polynomial.map_map]
  exact congrArg (fun f : ℤ →+* ZMod 3 => p.map f)
    (Int.quotientSpanNatEquivZMod_comp_Quotient_mk 3)

local instance coefficientDomain : IsDomain Q :=
  Function.Injective.isDomain coefficientRingEquiv.toRingHom coefficientRingEquiv.injective

@[expose] def coefficient (i : Fin 4) : Q :=
  algebraMap ℤ[X] Q (OriginalIntegerAffineModel318.coefficient twist i)

theorem untwisted_coefficient (i : Fin 4) :
    OriginalIntegerAffineModel318.coefficient twist i =
      X - C (OriginalIntegerAffineModel318.contacts i) := by
  norm_num [OriginalIntegerAffineModel318.coefficient, twist]

theorem coefficient_nonzero (i : Fin 4) : coefficient i ≠ 0 := by
  intro h
  have he := congrArg coefficientRingEquiv h
  change coefficientRingEquiv (Ideal.Quotient.mk I
    (OriginalIntegerAffineModel318.coefficient twist i)) = coefficientRingEquiv 0 at he
  rw [coefficientRingEquiv_mk, untwisted_coefficient, map_zero] at he
  have h1 := congrArg (fun p : (ZMod 3)[X] => p.coeff 1) he
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C,
    Polynomial.coeff_zero] at h1
  norm_num at h1

abbrev extendedIdeal : Ideal Order := I.map (algebraMap ℤ[X] Order)

theorem extendedIdeal_eq_three : extendedIdeal = Ideal.span {(3 : Order)} := by
  rw [extendedIdeal, I, Ideal.map_map, Ideal.map_span, Set.image_singleton]
  simp

/-- The actual order quotient by the extended coefficient ideal is the
actual four-root base change, with no claim that a generic algebra is a field. -/
@[expose] def quotientEquiv : (Order ⧸ extendedIdeal) ≃+*
    FourRootOrder318.Order coefficient :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Order I).toRingEquiv.trans
    (FourRootOrder318.baseChange (OriginalIntegerAffineModel318.coefficient twist) Q).toRingEquiv

/-- Reducedness is now for the literal original integral order modulo 3,
not merely for an abstract coefficient model with matching equations. -/
theorem actual_quotient_reduced : IsReduced (Order ⧸ Ideal.span {(3 : Order)}) := by
  letI : IsReduced (FourRootOrder318.Order coefficient) := by
    apply FourRootGenericReduced318.reduced coefficient
    · intro h
      have he := congrArg coefficientRingEquiv h
      have he' : (2 : (ZMod 3)[X]) = 0 := by
        simpa only [map_ofNat, map_zero] using he
      have h0 := congrArg (fun p : (ZMod 3)[X] => p.eval 0) he'
      norm_num at h0
    · exact coefficient_nonzero
  rw [← extendedIdeal_eq_three]
  exact isReduced_of_injective quotientEquiv.toRingHom quotientEquiv.injective

end OriginalPrimeThreeActualQuotient318
