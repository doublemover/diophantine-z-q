module

public import SelectedActualComplexPrincipalOpenScalarChange318
public import Mathlib.RingTheory.PolynomialAlgebra

public section

noncomputable section

open scoped Polynomial TensorProduct
open SelectedActualComplexPrincipalOpenScalarChange318

namespace SelectedActualComplexPolynomialOrdinaryBase318

universe u

variable (k C : Type u) [CommRing k] [CommRing C] [Algebra k C]

local instance : Algebra k[X] C[X] := Polynomial.algebra k C

abbrev mappedDenominator (d : k[X]) : C[X] := d.map (algebraMap k C)
abbrev baseRing (d : k[X]) := Localization.Away d
abbrev complexPolynomialBase (d : k[X]) := Localization.Away (mappedDenominator k C d)

private theorem tensorPolynomial_scalar (x : k[X]) :
    (polyEquivTensor' k C).symm ((1 : C) ⊗ₜ[k] x) = x.map (algebraMap k C) := by
  simp only [coe_polyEquivTensor'_symm, polyEquivTensor_symm_apply_tmul_eq_smul, one_smul]

private theorem polynomialOpenSubmonoid (d : k[X]) :
    (Submonoid.powers ((1 : C) ⊗ₜ[k] d)).map
      (polyEquivTensor' k C).symm.toRingEquiv.toMonoidHom =
        Submonoid.powers (mappedDenominator k C d) := by
  rw [Submonoid.map_powers]
  apply congrArg Submonoid.powers
  exact tensorPolynomial_scalar k C d

/-- The actual complex change of the old ordinary denominator open
is the ordinary complex polynomial open at its exact mapped denominator. -/
def scalarOrdinaryBase (d : k[X]) :
    C ⊗[k] baseRing k d ≃+* complexPolynomialBase k C d := by
  let S := k[X]
  let O := baseRing k d
  let W := C ⊗[k] O
  let V := complexPolynomialBase k C d
  letI : Algebra (C ⊗[k] S) W := (scalarOpenMap k C S O).toRingHom.toAlgebra
  letI : IsLocalization.Away ((1 : C) ⊗ₜ[k] d) W := scalar_change_principal_open k C S O d
  exact IsLocalization.ringEquivOfRingEquiv W V (polyEquivTensor' k C).symm.toRingEquiv
    (polynomialOpenSubmonoid k C d)

/-- Every polynomial on the old base maps by literal coefficient
extension, before the same distinguished element is inverted. -/
theorem scalarOrdinaryBase_polynomial (d x : k[X]) :
    scalarOrdinaryBase k C d ((1 : C) ⊗ₜ[k] (algebraMap k[X] (baseRing k d) x)) =
      algebraMap C[X] (complexPolynomialBase k C d) (x.map (algebraMap k C)) := by
  let S := k[X]
  let O := baseRing k d
  let W := C ⊗[k] O
  let V := complexPolynomialBase k C d
  letI : Algebra (C ⊗[k] S) W := (scalarOpenMap k C S O).toRingHom.toAlgebra
  letI : IsLocalization.Away ((1 : C) ⊗ₜ[k] d) W := scalar_change_principal_open k C S O d
  have h := IsLocalization.ringEquivOfRingEquiv_eq (S := W) (Q := V)
    (polynomialOpenSubmonoid k C d) ((1 : C) ⊗ₜ[k] x)
  have hx : algebraMap (C ⊗[k] S) W ((1 : C) ⊗ₜ[k] x) =
      (1 : C) ⊗ₜ[k] (algebraMap k[X] O x) := by
    change (scalarOpenMap k C S O) ((1 : C) ⊗ₜ[k] x) = _
    exact Algebra.TensorProduct.map_tmul _ _ 1 x
  have hc : (polyEquivTensor' k C).symm.toRingEquiv ((1 : C) ⊗ₜ[k] x) =
      x.map (algebraMap k C) := tensorPolynomial_scalar k C x
  rw [hx, hc] at h
  exact h

theorem scalarOrdinaryBase_parameter (d : k[X]) :
    scalarOrdinaryBase k C d ((1 : C) ⊗ₜ[k] (algebraMap k[X] (baseRing k d) Polynomial.X)) =
      algebraMap C[X] (complexPolynomialBase k C d) Polynomial.X := by
  rw [scalarOrdinaryBase_polynomial, Polynomial.map_X]

end SelectedActualComplexPolynomialOrdinaryBase318

#print axioms SelectedActualComplexPolynomialOrdinaryBase318.scalarOrdinaryBase_polynomial
#print axioms SelectedActualComplexPolynomialOrdinaryBase318.scalarOrdinaryBase_parameter
