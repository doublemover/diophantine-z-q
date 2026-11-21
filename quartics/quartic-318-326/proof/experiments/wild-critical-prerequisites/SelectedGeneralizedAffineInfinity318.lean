module
public import SelectedGeneralizedInfinityJets318
public import JacobianLocalSmooth318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.FinCases
public section
noncomputable section
open MvPolynomial Algebra

namespace SelectedGeneralizedAffineInfinity318

variable {R : Type*} [CommRing R]

/-- Explicit dehomogenization of the actual generalized projective
equation on Y≠0, with (t,z)=(X/Y,Z/Y) and d=J−1728. -/
@[expose] def equation (d : Rˣ) : MvPolynomial (Fin 2) R :=
  X 1 + X 0*X 1 - X 0^3 + C (36*(↑d⁻¹ : R))*X 0*X 1^2 +
    C (↑d⁻¹ : R)*X 1^3

@[expose] def equations (d : Rˣ) : Unit → MvPolynomial (Fin 2) R :=
  fun _ => equation d

abbrev Chart (d : Rˣ) := MvPolynomial (Fin 2) R ⧸ Ideal.span (Set.range (equations d))

@[expose] def parameter (d : Rˣ) : Chart d := Ideal.Quotient.mk _ (X 0)
@[expose] def ordinate (d : Rˣ) : Chart d := Ideal.Quotient.mk _ (X 1)

theorem dehomogenizes {D : Type*} [CommRing D] [Algebra R D] (d : Rˣ) (t z : D) :
    ((SelectedGeneralizedJCurve318.curve d).baseChange D).toProjective.Equation ![t,1,z] ↔
      MvPolynomial.aeval ![t,z] (equation d) = 0 := by
  rw [WeierstrassCurve.Projective.equation_iff]
  change (1:D)^2*z +(algebraMap R D 1)*t*1*z +(algebraMap R D 0)*1*z^2 -
    (t^3+(algebraMap R D 0)*t^2*z+(algebraMap R D (-36*(↑d⁻¹ : R)))*t*z^2+
      (algebraMap R D (-(↑d⁻¹ : R)))*z^3) = 0 ↔ _
  simp only [equation,map_add,map_sub,map_mul,map_pow,map_one,map_zero,map_neg,map_ofNat,
    MvPolynomial.aeval_X,MvPolynomial.aeval_C,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor <;> intro h
  · convert h using 1 <;> ring
  · convert h using 1 <;> ring

/-- The actual one-relation chart with independent variable t and
submersive coordinate z. -/
@[expose] def presentation (d : Rˣ) : PreSubmersivePresentation R (Chart d) (Fin 2) Unit :=
  PreSubmersivePresentation.naive (v := equations d) (fun _ => 1)
    (fun _ _ _ => Subsingleton.elim _ _)

theorem partial_ordinate (d : Rˣ) : pderiv 1 (equation d) =
    1 + X 0 + C (72*(↑d⁻¹ : R))*X 0*X 1 + C (3*(↑d⁻¹ : R))*X 1^2 := by
  simp [equation,C_mul]
  ring

/-- The origin is an actual augmentation of the specified chart ring. -/
@[expose] def origin (d : Rˣ) : Chart d →ₐ[R] R := by
  let h := MvPolynomial.aeval (fun _ : Fin 2 => (0:R))
  refine Ideal.Quotient.liftₐ _ h ?_
  intro f hf
  have hk : Ideal.span (Set.range (equations d)) ≤ RingHom.ker h.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨_,rfl⟩
    change h (equation d) = 0
    simp [h,equation]
  exact hk hf

@[simp] theorem origin_parameter (d : Rˣ) : origin d (parameter d) = 0 := by
  simp [origin,parameter,Ideal.Quotient.liftₐ_apply]

@[simp] theorem origin_ordinate (d : Rˣ) : origin d (ordinate d) = 0 := by
  simp [origin,ordinate,Ideal.Quotient.liftₐ_apply]

theorem origin_jacobian (d : Rˣ) : origin d (presentation d).jacobian = 1 := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp only [presentation,Matrix.det_unique,PreSubmersivePresentation.jacobiMatrix_naive,equations]
  change origin d (Ideal.Quotient.mk _ (pderiv 1 (equation d))) = 1
  rw [partial_ordinate]
  simp [origin,Ideal.Quotient.liftₐ_apply]

abbrev SmoothChart (d : Rˣ) := Localization.Away (presentation d).jacobian

instance smooth (d : Rˣ) : Algebra.Smooth R (SmoothChart d) := by
  have := JacobianLocalSmooth318.localization_jacobian (presentation d)
  infer_instance

/-- The same augmentation lands in the actual smooth neighborhood
because the derivative specializes to the literal scalar 1. -/
@[expose] def smoothOrigin (d : Rˣ) : SmoothChart d →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (f := origin d) (presentation d).jacobian
    (by rw [origin_jacobian]; exact isUnit_one)

end SelectedGeneralizedAffineInfinity318

#print axioms SelectedGeneralizedAffineInfinity318.dehomogenizes
#print axioms SelectedGeneralizedAffineInfinity318.smoothOrigin
