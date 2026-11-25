module
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial

@[expose] public section
noncomputable section

open Algebra Polynomial KaehlerDifferential TensorProduct
open scoped TensorProduct

namespace OriginalSameJCentredOrdinaryCotangent318

variable {k A : Type*} [Field k] [CommRing A]
  [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A]
  [Algebra.FormallyEtale k[X] A]

/-- True coefficient map in the ordinary normalized χ chart.
It is obtained from étale Kähler base change, with no frame chosen. -/
def coefficient : Ω[A⁄k] ≃ₗ[A] A :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k k[X] A).symm.trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A)
      (KaehlerDifferential.polynomialEquiv k)).trans
        (TensorProduct.AlgebraTensorModule.rid k[X] A A))

theorem polynomial_read (p : k[X]) :
    coefficient (D k A (algebraMap k[X] A p)) =
      algebraMap k[X] A (Polynomial.derivative p) := by
  rw [coefficient, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, polynomialEquiv_D,
    TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]

abbrev χ : A := algebraMap k[X] A (Polynomial.X : k[X])

abbrev u (n:k) : A := χ (k:=k) (A:=A) - algebraMap k A n

theorem literal_dχ : coefficient (D k A (χ (k:=k) (A:=A))) = 1 := by
  rw [polynomial_read,Polynomial.derivative_X,map_one]

theorem its_centred_du (n:k) : coefficient (D k A (u (A:=A) n)) = 1 := by
  change coefficient (D k A (χ (k:=k) (A:=A) - algebraMap k A n)) = 1
  rw [map_sub, (D k A).map_algebraMap, sub_zero, literal_dχ]

theorem genuine_form (n:k) (w : Ω[A⁄k]) : w = coefficient w • D k A (u (A:=A) n) := by
  apply (coefficient (k:=k) (A:=A)).injective
  rw [map_smul,its_centred_du,smul_eq_mul,mul_one]

/-- The same actual reciprocal differential is not identified by
a coordinate value alone. The proof consumes the full ring identity
χ·π=1 and reads ordinary dπ as −π² in the SAME dχ frame. -/
theorem reciprocal (π : A) (hπ : χ (k:=k) (A:=A)*π=1) :
    coefficient (D k A π) = -π^2 := by
  let z := coefficient (D k A π)
  let c : A := χ (k:=k) (A:=A)
  have hh : c*z + π = 0 := by
    have H := congrArg (fun a : A => coefficient (D k A a)) hπ
    rw [(D k A).leibniz, (D k A).map_one_eq_zero,
      map_add, map_smul, map_smul, literal_dχ, smul_eq_mul, smul_eq_mul, mul_one, map_zero] at H
    exact H
  have h := congrArg (fun w : A => π*w) hh
  change π*(c*z+π) = π*0 at h
  rw [mul_add, ←mul_assoc, mul_comm π c, hπ, one_mul, mul_zero] at h
  exact eq_neg_of_add_eq_zero_left h |>.trans (congrArg Neg.neg (pow_two π).symm)

end OriginalSameJCentredOrdinaryCotangent318

#print axioms OriginalSameJCentredOrdinaryCotangent318.polynomial_read
#print axioms OriginalSameJCentredOrdinaryCotangent318.genuine_form
#print axioms OriginalSameJCentredOrdinaryCotangent318.reciprocal
