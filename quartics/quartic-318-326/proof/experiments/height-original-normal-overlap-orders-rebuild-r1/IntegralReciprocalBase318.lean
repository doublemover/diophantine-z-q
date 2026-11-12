module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic
public section
noncomputable section
namespace IntegralReciprocalBase318
open Polynomial
set_option maxHeartbeats 900000
variable (R : Type*) [CommRing R] (a : Fin 4 → R) (N : R)
@[expose] def finiteDenominator : R[X] := C N * (X * ∏ i : Fin 4, (X-C (a i)))
@[expose] def reciprocalDenominator : R[X] := C N * (X * ∏ i : Fin 4, (1-C (a i)*X))
abbrev FiniteBase := Localization.Away (finiteDenominator R a N)
abbrev ReciprocalBase := Localization.Away (reciprocalDenominator R a N)
@[expose] def t : FiniteBase R a N := algebraMap R[X] (FiniteBase R a N) X
@[expose] def s : ReciprocalBase R a N := algebraMap R[X] (ReciprocalBase R a N) X
@[simp] theorem finite_C (r : R) :
    algebraMap R[X] (FiniteBase R a N) (C r) = algebraMap R (FiniteBase R a N) r :=
  (IsScalarTower.algebraMap_apply R R[X] (FiniteBase R a N) r).symm
@[simp] theorem reciprocal_C (r : R) :
    algebraMap R[X] (ReciprocalBase R a N) (C r) = algebraMap R (ReciprocalBase R a N) r :=
  (IsScalarTower.algebraMap_apply R R[X] (ReciprocalBase R a N) r).symm

theorem finite_constant_unit : IsUnit (algebraMap R (FiniteBase R a N) N) := by
  rw [←finite_C]
  exact IsLocalization.Away.isUnit_of_dvd (finiteDenominator R a N) (dvd_mul_right _ _)
theorem reciprocal_constant_unit : IsUnit (algebraMap R (ReciprocalBase R a N) N) := by
  rw [←reciprocal_C]
  exact IsLocalization.Away.isUnit_of_dvd (reciprocalDenominator R a N) (dvd_mul_right _ _)
theorem t_unit : IsUnit (t R a N) := by
  apply IsLocalization.Away.isUnit_of_dvd (finiteDenominator R a N)
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
theorem s_unit : IsUnit (s R a N) := by
  apply IsLocalization.Away.isUnit_of_dvd (reciprocalDenominator R a N)
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
@[expose] def tUnit : (FiniteBase R a N)ˣ := (t_unit R a N).unit
@[expose] def sUnit : (ReciprocalBase R a N)ˣ := (s_unit R a N).unit
@[simp] theorem tUnit_coe : (tUnit R a N : FiniteBase R a N) = t R a N :=
  (t_unit R a N).unit_spec
@[simp] theorem sUnit_coe : (sUnit R a N : ReciprocalBase R a N) = s R a N :=
  (s_unit R a N).unit_spec

theorem finite_factor_unit (i : Fin 4) :
    IsUnit (t R a N - algebraMap R (FiniteBase R a N) (a i)) := by
  have h : IsUnit (algebraMap R[X] (FiniteBase R a N) (X-C (a i))) := by
    apply IsLocalization.Away.isUnit_of_dvd (finiteDenominator R a N)
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _) _
  simpa [t] using h
theorem reciprocal_factor_unit (i : Fin 4) :
    IsUnit (1-algebraMap R (ReciprocalBase R a N) (a i)*s R a N) := by
  have h : IsUnit (algebraMap R[X] (ReciprocalBase R a N) (1-C (a i)*X)) := by
    apply IsLocalization.Away.isUnit_of_dvd (reciprocalDenominator R a N)
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _) _
  simpa [s] using h

theorem to_finite_factor_unit (i : Fin 4) :
    IsUnit ((↑(sUnit R a N)⁻¹ : ReciprocalBase R a N) -
      algebraMap R (ReciprocalBase R a N) (a i)) := by
  have h : (↑(sUnit R a N)⁻¹ : ReciprocalBase R a N) -
      algebraMap R (ReciprocalBase R a N) (a i) =
      ↑(sUnit R a N)⁻¹ * (1-algebraMap R (ReciprocalBase R a N) (a i)*s R a N) := by
    rw [←sUnit_coe]
    simp only [mul_sub, mul_one]
    rw [mul_left_comm, Units.inv_mul, mul_one]
  rw [h]
  exact (sUnit R a N)⁻¹.isUnit.mul (reciprocal_factor_unit R a N i)
theorem to_reciprocal_factor_unit (i : Fin 4) :
    IsUnit (1-algebraMap R (FiniteBase R a N) (a i)*
      (↑(tUnit R a N)⁻¹ : FiniteBase R a N)) := by
  have h : 1-algebraMap R (FiniteBase R a N) (a i)*
      (↑(tUnit R a N)⁻¹ : FiniteBase R a N) =
      (t R a N-algebraMap R (FiniteBase R a N) (a i))*↑(tUnit R a N)⁻¹ := by
    rw [←tUnit_coe]
    simp only [sub_mul, Units.mul_inv]
  rw [h]
  exact (finite_factor_unit R a N i).mul (tUnit R a N)⁻¹.isUnit
@[expose] def finitePolynomial : R[X] →+* ReciprocalBase R a N :=
  (Polynomial.aeval (↑(sUnit R a N)⁻¹ : ReciprocalBase R a N)).toRingHom
@[expose] def reciprocalPolynomial : R[X] →+* FiniteBase R a N :=
  (Polynomial.aeval (↑(tUnit R a N)⁻¹ : FiniteBase R a N)).toRingHom

theorem finite_denominator_unit :
    IsUnit (finitePolynomial R a N (finiteDenominator R a N)) := by
  simpa [finitePolynomial, finiteDenominator] using
    (reciprocal_constant_unit R a N).mul ((sUnit R a N)⁻¹.isUnit.mul
      (IsUnit.prod_univ_iff.mpr (to_finite_factor_unit R a N)))
theorem reciprocal_denominator_unit :
    IsUnit (reciprocalPolynomial R a N (reciprocalDenominator R a N)) := by
  simpa [reciprocalPolynomial, reciprocalDenominator] using
    (finite_constant_unit R a N).mul ((tUnit R a N)⁻¹.isUnit.mul
      (IsUnit.prod_univ_iff.mpr (to_reciprocal_factor_unit R a N)))
@[expose] def forward : FiniteBase R a N →+* ReciprocalBase R a N :=
  IsLocalization.Away.lift (g := finitePolynomial R a N)
    (finiteDenominator R a N) (finite_denominator_unit R a N)
@[expose] def backward : ReciprocalBase R a N →+* FiniteBase R a N :=
  IsLocalization.Away.lift (g := reciprocalPolynomial R a N)
    (reciprocalDenominator R a N) (reciprocal_denominator_unit R a N)
@[simp] theorem forward_map (p : R[X]) :
    forward R a N (algebraMap R[X] (FiniteBase R a N) p) = finitePolynomial R a N p :=
  IsLocalization.Away.lift_eq _ _ p
@[simp] theorem backward_map (p : R[X]) :
    backward R a N (algebraMap R[X] (ReciprocalBase R a N) p) = reciprocalPolynomial R a N p :=
  IsLocalization.Away.lift_eq _ _ p
@[simp] theorem forward_t : forward R a N (t R a N) = ↑(sUnit R a N)⁻¹ := by
  simp [t, finitePolynomial]
@[simp] theorem backward_s : backward R a N (s R a N) = ↑(tUnit R a N)⁻¹ := by
  simp [s, reciprocalPolynomial]
theorem forward_inverse : forward R a N (↑(tUnit R a N)⁻¹) = s R a N := by
  have h := congrArg (forward R a N) (Units.mul_inv (tUnit R a N))
  rw [map_mul, map_one, tUnit_coe, forward_t] at h
  simpa only [inv_inv, sUnit_coe] using (Units.inv_eq_of_mul_eq_one_right h).symm
theorem backward_inverse : backward R a N (↑(sUnit R a N)⁻¹) = t R a N := by
  have h := congrArg (backward R a N) (Units.mul_inv (sUnit R a N))
  rw [map_mul, map_one, sUnit_coe, backward_s] at h
  simpa only [inv_inv, tUnit_coe] using (Units.inv_eq_of_mul_eq_one_right h).symm
theorem backward_forward : (backward R a N).comp (forward R a N) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (finiteDenominator R a N))
  apply Polynomial.ringHom_ext
  · intro r
    simp [finitePolynomial, reciprocalPolynomial]
  · simp [t, finitePolynomial, backward_inverse]
theorem forward_backward : (forward R a N).comp (backward R a N) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (reciprocalDenominator R a N))
  apply Polynomial.ringHom_ext
  · intro r
    simp [finitePolynomial, reciprocalPolynomial]
  · simp [s, reciprocalPolynomial, forward_inverse]

/-- Literal inversion of the coordinate, preserving the same arithmetic
constant N. Neither a characteristic-zero field nor an invertible N is
assumed in the unlocalized coefficient ring. -/
@[expose] def reciprocalEquiv : FiniteBase R a N ≃+* ReciprocalBase R a N :=
  { forward R a N with
    invFun := backward R a N
    left_inv := fun x => RingHom.congr_fun (backward_forward R a N) x
    right_inv := fun x => RingHom.congr_fun (forward_backward R a N) x }

theorem finiteDenominator_ne_zero [IsDomain R] (hN : N ≠ 0) :
    finiteDenominator R a N ≠ 0 :=
  mul_ne_zero (Polynomial.C_ne_zero.mpr hN) (mul_ne_zero Polynomial.X_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)))
theorem reciprocalDenominator_ne_zero [IsDomain R] (hN : N ≠ 0) :
    reciprocalDenominator R a N ≠ 0 := by
  apply mul_ne_zero (Polynomial.C_ne_zero.mpr hN)
  apply mul_ne_zero Polynomial.X_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ h
  have e := congrArg (Polynomial.eval (0 : R)) h
  norm_num at e
end IntegralReciprocalBase318
