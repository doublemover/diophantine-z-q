module
public import SelectedGeneralizedAffineJacobianCover318
public section
noncomputable section
open MvPolynomial Algebra
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedProjectiveOverlap318

namespace SelectedGeneralizedLocalizedOverlap318

variable {R : Type*} [CommRing R]

abbrev UZ (d : Rˣ) := Localization.Away (y d)
abbrev UY (d : Rˣ) := Localization.Away (ordinate d)

@[expose] def ax (d : Rˣ) : UZ d := algebraMap (FiniteChart d) (UZ d) (x d)
@[expose] def ay (d : Rˣ) : UZ d := algebraMap (FiniteChart d) (UZ d) (y d)
@[expose] def ai (d : Rˣ) : UZ d := IsLocalization.Away.invSelf (y d)
@[expose] def it (d : Rˣ) : UY d := algebraMap (Chart d) (UY d) (parameter d)
@[expose] def iz (d : Rˣ) : UY d := algebraMap (Chart d) (UY d) (ordinate d)
@[expose] def ii (d : Rˣ) : UY d := IsLocalization.Away.invSelf (ordinate d)

@[simp] theorem ay_ai (d : Rˣ) : ay d*ai d=1 := IsLocalization.Away.mul_invSelf _
@[simp] theorem iz_ii (d : Rˣ) : iz d*ii d=1 := IsLocalization.Away.mul_invSelf _

theorem relation_UZ (d : Rˣ) : finiteValue d (ax d) (ay d)=0 := by
  have h := congrArg (algebraMap (FiniteChart d) (UZ d))
    (SelectedGeneralizedAffineJacobianCover318.finite_relation d)
  simpa only [finiteValue,map_sub,map_pow,map_mul,map_add,map_zero,
    ← IsScalarTower.algebraMap_apply,ax,ay] using h

theorem relation_UY (d : Rˣ) : infinityValue d (it d) (iz d)=0 := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (equations d))) (equation d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨(),rfl⟩)
  have hi : infinityValue d (parameter d) (ordinate d) = 0 := by
    simp only [equation,map_add,map_sub,map_mul,map_pow] at h
    exact h
  have hh := congrArg (algebraMap (Chart d) (UY d)) hi
  simpa only [infinityValue,map_sub,map_pow,map_mul,map_add,map_zero,
    ← IsScalarTower.algebraMap_apply,it,iz] using hh

/-- Actual rescaling maps on the projective coordinate algebras. -/
@[expose] def toUYbase (d : Rˣ) : FiniteChart d →ₐ[R] UY d :=
  finiteLift d (it d*ii d) (ii d) (by
    rw [infinity_to_finite d _ _ _ (iz_ii d),relation_UY,mul_zero])

@[expose] def toUZbase (d : Rˣ) : Chart d →ₐ[R] UZ d :=
  infinityLift d (ax d*ai d) (ai d) (by
    rw [finite_to_infinity d _ _ _ (ay_ai d),relation_UZ,mul_zero])

@[expose] def toUY (d : Rˣ) : UZ d →ₐ[R] UY d :=
  IsLocalization.Away.liftAlgHom (f := toUYbase d) (y d) (by
    change IsUnit (finiteLift d (it d*ii d) (ii d) _ (y d))
    rw [finiteLift_y]
    exact IsUnit.of_mul_eq_one_right _ (iz_ii d))

@[expose] def toUZ (d : Rˣ) : UY d →ₐ[R] UZ d :=
  IsLocalization.Away.liftAlgHom (f := toUZbase d) (ordinate d) (by
    change IsUnit (infinityLift d (ax d*ai d) (ai d) _ (ordinate d))
    rw [infinityLift_z]
    exact IsUnit.of_mul_eq_one_right _ (ay_ai d))

theorem toUY_map (d : Rˣ) (a : FiniteChart d) :
    toUY d (algebraMap (FiniteChart d) (UZ d) a) = toUYbase d a := by
  rw [toUY,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
theorem toUZ_map (d : Rˣ) (a : Chart d) :
    toUZ d (algebraMap (Chart d) (UY d) a) = toUZbase d a := by
  rw [toUZ,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]

@[simp] theorem toUY_ax (d : Rˣ) : toUY d (ax d)=it d*ii d := by
  rw [ax,toUY_map,toUYbase,finiteLift_x]
@[simp] theorem toUY_ay (d : Rˣ) : toUY d (ay d)=ii d := by
  rw [ay,toUY_map,toUYbase,finiteLift_y]
@[simp] theorem toUZ_it (d : Rˣ) : toUZ d (it d)=ax d*ai d := by
  rw [it,toUZ_map,toUZbase,infinityLift_t]
@[simp] theorem toUZ_iz (d : Rˣ) : toUZ d (iz d)=ai d := by
  rw [iz,toUZ_map,toUZbase,infinityLift_z]

@[simp] theorem toUY_ai (d : Rˣ) : toUY d (ai d)=iz d := by
  have h := congrArg (toUY d) (ay_ai d)
  simp only [map_mul,map_one,toUY_ay] at h
  calc
    _ = (iz d*ii d)*toUY d (ai d) := by rw [iz_ii,one_mul]
    _ = iz d*(ii d*toUY d (ai d)) := mul_assoc _ _ _
    _ = _ := by rw [h,mul_one]

@[simp] theorem toUZ_ii (d : Rˣ) : toUZ d (ii d)=ay d := by
  have h := congrArg (toUZ d) (iz_ii d)
  simp only [map_mul,map_one,toUZ_iz] at h
  calc
    _ = (ay d*ai d)*toUZ d (ii d) := by rw [ay_ai,one_mul]
    _ = ay d*(ai d*toUZ d (ii d)) := mul_assoc _ _ _
    _ = _ := by rw [h,mul_one]

theorem inverse_UZ (d : Rˣ) :
    (toUZ d).comp (toUY d) = AlgHom.id R (UZ d) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (y d))
  apply finite_ext d
  · change toUZ d (toUY d (ax d)) = ax d
    simp only [toUY_ax,map_mul,toUZ_it,toUZ_ii]
    rw [mul_assoc,mul_comm (ai d) (ay d),ay_ai,mul_one]
  · change toUZ d (toUY d (ay d)) = ay d
    rw [toUY_ay,toUZ_ii]

theorem inverse_UY (d : Rˣ) :
    (toUY d).comp (toUZ d) = AlgHom.id R (UY d) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (ordinate d))
  apply infinity_ext d
  · change toUY d (toUZ d (it d)) = it d
    simp only [toUZ_it,map_mul,toUY_ax,toUY_ai]
    rw [mul_assoc,mul_comm (ii d) (iz d),iz_ii,mul_one]
  · change toUY d (toUZ d (iz d)) = iz d
    rw [toUZ_iz,toUY_ai]

/-- The literal two affine charts have the same reciprocal open. -/
@[expose] def overlap (d : Rˣ) : UY d ≃ₐ[R] UZ d :=
  AlgEquiv.ofAlgHom (toUZ d) (toUY d) (inverse_UZ d) (inverse_UY d)

end SelectedGeneralizedLocalizedOverlap318

#print axioms SelectedGeneralizedLocalizedOverlap318.overlap
