module
public import ContactProjectiveModel318
public section
noncomputable section
namespace ContactReciprocalBase318
open Polynomial
open ContactKummerOrder318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev a := LinearContactSquareclass318.contacts
@[expose] def denominator : R := X*∏i:Fin 4,(1-C (a i)*X)
abbrev Base := Localization.Away denominator
@[expose] def s : Base := algebraMap R Base X
@[expose] def t : OpenBase := algebraMap R OpenBase X
@[expose] def tUnit : OpenBaseˣ := ContactProjectiveModel318.base_t_unit.unit
@[simp] theorem tUnit_coe : (tUnit:OpenBase)=t := ContactProjectiveModel318.base_t_unit.unit_spec

@[simp] theorem base_C (q:ℚ) : algebraMap R Base (C q)=algebraMap ℚ Base q :=
  (IsScalarTower.algebraMap_apply ℚ R Base q).symm
@[simp] theorem openBase_C (q:ℚ) : algebraMap R OpenBase (C q)=algebraMap ℚ OpenBase q :=
  (IsScalarTower.algebraMap_apply ℚ R OpenBase q).symm

theorem s_unit : IsUnit s := by
  apply IsLocalization.Away.isUnit_of_dvd denominator
  exact dvd_mul_right _ _
@[expose] def sUnit : Baseˣ := s_unit.unit
@[simp] theorem sUnit_coe : (sUnit:Base)=s := s_unit.unit_spec

theorem reciprocal_factor_unit (i:Fin 4) : IsUnit (1-algebraMap ℚ Base (a i)*s) := by
  have h: IsUnit (algebraMap R Base (1-C (a i)*X)) := by
    apply IsLocalization.Away.isUnit_of_dvd denominator
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
  simpa [s] using h

theorem original_factor_unit (i:Fin 4) : IsUnit (t-algebraMap ℚ OpenBase (a i)) := by
  have h: IsUnit (algebraMap R OpenBase (X-C (a i))) := by
    apply IsLocalization.Away.isUnit_of_dvd ContactKummerOrder318.denominator
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  simpa [t] using h

theorem to_original_factor_unit (i:Fin 4) :
    IsUnit ((↑sUnit⁻¹:Base)-algebraMap ℚ Base (a i)) := by
  have h:(↑sUnit⁻¹:Base)-algebraMap ℚ Base (a i)=
      ↑sUnit⁻¹*(1-algebraMap ℚ Base (a i)*s) := by
    rw [←sUnit_coe]
    simp only [mul_sub,mul_one]
    rw [mul_left_comm,Units.inv_mul,mul_one]
  rw [h]
  exact sUnit⁻¹.isUnit.mul (reciprocal_factor_unit i)

theorem to_reciprocal_factor_unit (i:Fin 4) :
    IsUnit (1-algebraMap ℚ OpenBase (a i)*(↑tUnit⁻¹:OpenBase)) := by
  have h:1-algebraMap ℚ OpenBase (a i)*(↑tUnit⁻¹:OpenBase)=
      (t-algebraMap ℚ OpenBase (a i))*↑tUnit⁻¹ := by
    rw [←tUnit_coe]
    simp only [sub_mul,Units.mul_inv]
  rw [h]
  exact (original_factor_unit i).mul tUnit⁻¹.isUnit

@[expose] def originalPolynomial : R→+*Base := (Polynomial.aeval (↑sUnit⁻¹:Base)).toRingHom
@[expose] def reciprocalPolynomial : R→+*OpenBase := (Polynomial.aeval (↑tUnit⁻¹:OpenBase)).toRingHom

theorem original_denominator_unit :
    IsUnit (originalPolynomial ContactKummerOrder318.denominator) := by
  simpa [originalPolynomial,ContactKummerOrder318.denominator] using
    (IsUnit.prod_univ_iff.mpr to_original_factor_unit)
theorem reciprocal_denominator_unit : IsUnit (reciprocalPolynomial denominator) := by
  simpa [reciprocalPolynomial,denominator] using
    tUnit⁻¹.isUnit.mul (IsUnit.prod_univ_iff.mpr to_reciprocal_factor_unit)

@[expose] def forward : OpenBase→+*Base :=
  IsLocalization.Away.lift (g:=originalPolynomial) ContactKummerOrder318.denominator original_denominator_unit
@[expose] def backward : Base→+*OpenBase :=
  IsLocalization.Away.lift (g:=reciprocalPolynomial) denominator reciprocal_denominator_unit

@[simp] theorem forward_map (p:R) : forward (algebraMap R OpenBase p)=originalPolynomial p :=
  IsLocalization.Away.lift_eq _ _ p
@[simp] theorem backward_map (p:R) : backward (algebraMap R Base p)=reciprocalPolynomial p :=
  IsLocalization.Away.lift_eq _ _ p
@[simp] theorem forward_t : forward t=↑sUnit⁻¹ := by simp [t,originalPolynomial]
@[simp] theorem backward_s : backward s=↑tUnit⁻¹ := by simp [s,reciprocalPolynomial]

theorem forward_inverse : forward (↑tUnit⁻¹)=s := by
  have h:=congrArg forward (Units.mul_inv tUnit)
  rw [map_mul,map_one,tUnit_coe,forward_t] at h
  exact (Units.inv_eq_of_mul_eq_one_right h).symm
theorem backward_inverse : backward (↑sUnit⁻¹)=t := by
  have h:=congrArg backward (Units.mul_inv sUnit)
  rw [map_mul,map_one,sUnit_coe,backward_s] at h
  exact (Units.inv_eq_of_mul_eq_one_right h).symm

theorem backward_forward : backward.comp forward=RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers ContactKummerOrder318.denominator)
  apply Polynomial.ringHom_ext
  · intro q
    simp [originalPolynomial,reciprocalPolynomial]
  · simp [t,originalPolynomial,backward_inverse]
theorem forward_backward : forward.comp backward=RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers denominator)
  apply Polynomial.ringHom_ext
  · intro q
    simp [originalPolynomial,reciprocalPolynomial]
  · simp [s,reciprocalPolynomial,forward_inverse]

@[expose] def reciprocalEquiv : OpenBase≃+*Base :=
  { forward with
    invFun:=backward
    left_inv:=fun x=>RingHom.congr_fun backward_forward x
    right_inv:=fun x=>RingHom.congr_fun forward_backward x }

theorem denominator_ne_zero : denominator≠0 := by
  apply mul_ne_zero Polynomial.X_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ h
  have e:=congrArg (Polynomial.eval (0:ℚ)) h
  norm_num at e
end ContactReciprocalBase318
