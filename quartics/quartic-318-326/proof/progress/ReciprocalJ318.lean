module
public import OpenJModel318
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace ReciprocalJ318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def denominator (N:ℕ) : Polynomial ℤ :=
  (6*(N:Polynomial ℤ))*Polynomial.X*(1-1728*Polynomial.X)
abbrev Base (N:ℕ) := Localization.Away (denominator N)
@[expose] def coord (N:ℕ) : Base N := algebraMap (Polynomial ℤ) (Base N) Polynomial.X

lemma units (N:ℕ) : IsUnit (6*(N:Base N)) ∧ IsUnit (coord N) ∧
    IsUnit (1-1728*coord N) := by
  have h:=IsLocalization.Away.algebraMap_isUnit (S:=Base N) (denominator N)
  simpa only [denominator,map_mul,map_sub,map_one,map_ofNat,map_natCast,coord,
    IsUnit.mul_iff,and_assoc] using h

@[expose] def zeroUnit (N:ℕ) : (OpenJModel318.Base N)ˣ :=
  (OpenJModel318.base_units N).2.2.2.1.unit
@[expose] def infinityUnit (N:ℕ) : (Base N)ˣ := (units N).2.1.unit
@[simp] lemma zeroUnit_coe (N:ℕ) : (zeroUnit N:OpenJModel318.Base N)=OpenJModel318.jCoord N :=
  (OpenJModel318.base_units N).2.2.2.1.unit_spec
@[simp] lemma infinityUnit_coe (N:ℕ) : (infinityUnit N:Base N)=coord N :=
  (units N).2.1.unit_spec

lemma infinity_to_zero_unit (N:ℕ) :
    IsUnit ((↑(infinityUnit N)⁻¹:Base N)-1728) := by
  have e : (↑(infinityUnit N)⁻¹:Base N)-1728=
      ↑(infinityUnit N)⁻¹*(1-1728*coord N) := by
    rw [←infinityUnit_coe]
    simp only [mul_sub,mul_one]
    rw [mul_left_comm,Units.inv_mul, mul_one]
  rw [e]
  exact ((infinityUnit N)⁻¹).isUnit.mul (units N).2.2

lemma zero_to_infinity_unit (N:ℕ) :
    IsUnit (1-1728*(↑(zeroUnit N)⁻¹:OpenJModel318.Base N)) := by
  have e : 1-1728*(↑(zeroUnit N)⁻¹:OpenJModel318.Base N)=
      (OpenJModel318.jCoord N-1728)*↑(zeroUnit N)⁻¹ := by
    rw [←zeroUnit_coe]
    simp only [sub_mul,Units.mul_inv]
  rw [e]
  exact (OpenJModel318.base_units N).2.2.2.2.mul ((zeroUnit N)⁻¹).isUnit

@[expose] def zeroPolynomial (N:ℕ) : Polynomial ℤ→+*Base N :=
  Polynomial.eval₂RingHom (Int.castRingHom (Base N)) ↑(infinityUnit N)⁻¹
@[expose] def infinityPolynomial (N:ℕ) : Polynomial ℤ→+*OpenJModel318.Base N :=
  Polynomial.eval₂RingHom (Int.castRingHom (OpenJModel318.Base N)) ↑(zeroUnit N)⁻¹

lemma zero_denominator_unit (N:ℕ) : IsUnit (zeroPolynomial N (OpenJModel318.denominator N)) := by
  simpa [zeroPolynomial,OpenJModel318.denominator] using
    ((units N).1.mul ((infinityUnit N)⁻¹).isUnit).mul (infinity_to_zero_unit N)
lemma infinity_denominator_unit (N:ℕ) : IsUnit (infinityPolynomial N (denominator N)) := by
  have hsix : IsUnit (6*(N:OpenJModel318.Base N)) := by
    have h:=((OpenJModel318.base_units N).1.mul (OpenJModel318.base_units N).2.1).mul
      (OpenJModel318.base_units N).2.2.1
    convert h using 1 <;> norm_num
  simpa [infinityPolynomial,denominator] using
    (hsix.mul ((zeroUnit N)⁻¹).isUnit).mul (zero_to_infinity_unit N)

@[expose] def forward (N:ℕ) : OpenJModel318.Base N→+*Base N :=
  IsLocalization.Away.lift (OpenJModel318.denominator N) (zero_denominator_unit N)
@[expose] def backward (N:ℕ) : Base N→+*OpenJModel318.Base N :=
  IsLocalization.Away.lift (denominator N) (infinity_denominator_unit N)

@[simp] lemma forward_map (N:ℕ) (p:Polynomial ℤ) :
    forward N (algebraMap (Polynomial ℤ) (OpenJModel318.Base N) p)=zeroPolynomial N p :=
  IsLocalization.Away.lift_eq _ _ p
@[simp] lemma backward_map (N:ℕ) (p:Polynomial ℤ) :
    backward N (algebraMap (Polynomial ℤ) (Base N) p)=infinityPolynomial N p :=
  IsLocalization.Away.lift_eq _ _ p
@[simp] lemma forward_coord (N:ℕ) : forward N (OpenJModel318.jCoord N)=↑(infinityUnit N)⁻¹ := by
  simp [OpenJModel318.jCoord,zeroPolynomial]
@[simp] lemma backward_coord (N:ℕ) : backward N (coord N)=↑(zeroUnit N)⁻¹ := by
  simp [coord,infinityPolynomial]

lemma forward_inverse (N:ℕ) : forward N (↑(zeroUnit N)⁻¹)=coord N := by
  have h:=congrArg (forward N) (Units.mul_inv (zeroUnit N))
  rw [map_mul,map_one,zeroUnit_coe,forward_coord] at h
  exact (Units.inv_eq_of_mul_eq_one_right h).symm
lemma backward_inverse (N:ℕ) : backward N (↑(infinityUnit N)⁻¹)=OpenJModel318.jCoord N := by
  have h:=congrArg (backward N) (Units.mul_inv (infinityUnit N))
  rw [map_mul,map_one,infinityUnit_coe,backward_coord] at h
  exact (Units.inv_eq_of_mul_eq_one_right h).symm

lemma backward_forward (N:ℕ) : (backward N).comp (forward N)=RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (OpenJModel318.denominator N))
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp [OpenJModel318.jCoord,zeroPolynomial,backward_inverse]

lemma forward_backward (N:ℕ) : (forward N).comp (backward N)=RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator N))
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp [coord,infinityPolynomial,forward_inverse]

/-- The actual two punctured polynomial coordinate rings are isomorphic;
this is not a rational-function-field substitution premise. -/
@[expose] def reciprocalEquiv (N:ℕ) : OpenJModel318.Base N≃+*Base N :=
  { forward N with
    invFun := backward N
    left_inv := fun x => RingHom.congr_fun (backward_forward N) x
    right_inv := fun x => RingHom.congr_fun (forward_backward N) x }

end ReciprocalJ318
