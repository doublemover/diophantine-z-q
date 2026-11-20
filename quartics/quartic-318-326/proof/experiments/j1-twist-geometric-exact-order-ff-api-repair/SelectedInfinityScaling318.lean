module
public import SelectedShortAffineScaling318
public section
noncomputable section
open WeierstrassOverlap318

namespace SelectedInfinityScaling318
variable {R : Type*} [CommRing R]
variable (A B C D : R) (r : Rˣ)
variable (hA : A = (r:R)^4*C) (hB : B = (r:R)^6*D)

theorem inverse_coeff (n : ℕ) (a b : R) (h : a = (r:R)^n*b) :
    b = (↑r⁻¹:R)^n*a := by
  rw [h,←mul_assoc,←mul_pow,Units.inv_mul,one_pow,one_mul]

private theorem inverse_scalar {S : Type*} [CommRing S] [Algebra R S] :
    algebraMap R S (↑r⁻¹:R) * algebraMap R S (r:R) = 1 := by
  rw [←map_mul,Units.inv_mul,map_one]

private theorem forward_scalar {S : Type*} [CommRing S] [Algebra R S] :
    algebraMap R S (r:R) * algebraMap R S (↑r⁻¹:R) = 1 := by
  rw [←map_mul,Units.mul_inv,map_one]

private theorem weighted_relation {S : Type*} [CommRing S]
    (u i a b x z : S) (h : u*i=1) :
    i^3*z-(i*x)^3-(u^4*a)*(i*x)*(i^3*z)^2-(u^6*b)*(i^3*z)^3 =
      i^3*(z-x^3-a*x*z^2-b*z^3) := by
  calc
    _ = i^3*z-i^3*x^3-(u*i)^4*i^3*a*x*z^2-(u*i)^6*i^3*b*z^3 := by ring
    _ = _ := by rw [h]; ring

local notation "I" => Infinity C D
local notation "j" => algebraMap R I (↑r⁻¹:R)

/-- Homogeneous rescaling [X:Y:Z] ↦ [r²X:r³Y:Z] on the actual
Y=1 chart, where (x,z) pull back to (r⁻¹x,r⁻³z). -/
@[expose] def infinityHom : Infinity A B →ₐ[R] Infinity C D :=
  InfinityChart318.lift A B (j*InfinityChart318.x C D) (j^3*InfinityChart318.z C D) (by
    rw [hA,hB]
    simp only [map_mul,map_pow]
    rw [weighted_relation _ _ _ _ _ _ (forward_scalar r),InfinityChart318.relation,mul_zero])

@[simp] theorem infinityHom_x :
    infinityHom A B C D r hA hB (InfinityChart318.x A B) = j*InfinityChart318.x C D :=
  InfinityChart318.lift_x ..

@[simp] theorem infinityHom_z :
    infinityHom A B C D r hA hB (InfinityChart318.z A B) = j^3*InfinityChart318.z C D :=
  InfinityChart318.lift_z ..

/-- The conventional parameter t=−X/Y=−x/y is preserved with
exact weight r⁻¹, not r, r⁻², or a sign change. -/
theorem parameter_t :
    infinityHom A B C D r hA hB (-InfinityChart318.x A B) =
      j*(-InfinityChart318.x C D) := by
  simp only [map_neg,infinityHom_x,mul_neg]

theorem origin_compat :
    (InfinityChart318.origin C D).comp (infinityHom A B C D r hA hB) =
      InfinityChart318.origin A B := by
  apply InfinityChart318.hom_ext <;>
    simp only [AlgHom.comp_apply,infinityHom_x,infinityHom_z,map_mul,InfinityChart318.origin_x,
      InfinityChart318.origin_z,mul_zero]

private theorem multiply_cancel {S : Type*} [CommRing S] [Algebra R S] (n : ℕ) (t : S) :
    (algebraMap R S (r:R))^n * ((algebraMap R S (↑r⁻¹:R))^n*t) = t := by
  rw [←mul_assoc,←mul_pow,forward_scalar,one_pow,one_mul]

include hA hB in
theorem infinity_comp_inverse :
    (infinityHom A B C D r hA hB).comp
      (infinityHom C D A B r⁻¹ (inverse_coeff r 4 A C hA) (inverse_coeff r 6 B D hB)) =
      AlgHom.id R (Infinity C D) := by
  apply InfinityChart318.hom_ext
  · have hh := multiply_cancel r 1 (InfinityChart318.x C D)
    simp only [pow_one] at hh
    simpa only [AlgHom.comp_apply,infinityHom_x,map_mul,AlgHom.commutes,inv_inv,AlgHom.id_apply] using hh
  · simpa only [AlgHom.comp_apply,infinityHom_z,map_mul,map_pow,AlgHom.commutes,inv_inv,
      AlgHom.id_apply] using multiply_cancel r 3 (InfinityChart318.z C D)

local notation "L" => InfinityOverlap C D
local notation "w" => algebraMap R L (r:R)
local notation "v" => algebraMap R L (↑r⁻¹:R)
local notation "F" => infinityHom A B C D r hA hB
local notation "l₀" => IsScalarTower.toAlgHom R (Infinity C D) (InfinityOverlap C D)
local notation "l₁" => IsScalarTower.toAlgHom R (Infinity A B) (InfinityOverlap A B)

/-- The true principal overlap D(z). Its new z differs from the
old z by the displayed cubic inverse unit. -/
@[expose] def overlapHom : InfinityOverlap A B →ₐ[R] InfinityOverlap C D :=
  IsLocalization.Away.liftAlgHom (f := l₀.comp F) (InfinityChart318.z A B) (by
    simp only [AlgHom.comp_apply,infinityHom_z,map_mul,map_pow,AlgHom.commutes]
    exact (((r⁻¹).isUnit.map (algebraMap R L)).pow 3).mul
      (IsLocalization.Away.algebraMap_isUnit (S:=L) (InfinityChart318.z C D)))

local notation "G" => overlapHom A B C D r hA hB

theorem infinity_overlap : G.comp l₁ = l₀.comp F := by
  apply AlgHom.ext
  intro t
  simp [overlapHom,IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem overlap_ix : G (ix A B) = v*ix C D := by
  have h := DFunLike.congr_fun (infinity_overlap A B C D r hA hB) (InfinityChart318.x A B)
  simpa only [AlgHom.comp_apply,infinityHom_x,map_mul,AlgHom.commutes,ix] using h

@[simp] theorem overlap_iz : G (iz A B) = v^3*iz C D := by
  have h := DFunLike.congr_fun (infinity_overlap A B C D r hA hB) (InfinityChart318.z A B)
  simpa only [AlgHom.comp_apply,infinityHom_z,map_mul,map_pow,AlgHom.commutes,iz] using h

@[simp] theorem overlap_ii : G (ii A B) = w^3*ii C D := by
  have h := congrArg G (iz_ii A B)
  simp only [map_mul,map_one,overlap_iz] at h
  apply ((((r⁻¹).isUnit.map (algebraMap R L)).pow 3).mul
    (IsUnit.of_mul_eq_one (ii C D) (iz_ii C D))).mul_left_cancel
  calc
    _ = 1 := h
    _ = _ := by
      symm
      calc
        _ = (v*w)^3*(iz C D*ii C D) := by ring
        _ = 1 := by rw [inverse_scalar,iz_ii,one_pow,one_mul]

theorem affine_overlap :
    G.comp (toInfinityBase A B) =
      (toInfinityBase C D).comp (SelectedShortAffineScaling318.hom A B C D r hA hB) := by
  apply affine_hom_ext
  · simp only [AlgHom.comp_apply,toInfinityBase_x,map_mul,overlap_ix,overlap_ii,
      SelectedShortAffineScaling318.hom_x,map_pow,AlgHom.commutes]
    calc
      _ = (v*w)*(w^2*(ix C D*ii C D)) := by ring
      _ = _ := by rw [inverse_scalar,one_mul]
  · simp only [AlgHom.comp_apply,toInfinityBase_y,overlap_ii,SelectedShortAffineScaling318.hom_y,
      map_mul,map_pow,AlgHom.commutes]

end SelectedInfinityScaling318

#print axioms SelectedInfinityScaling318.parameter_t
#print axioms SelectedInfinityScaling318.origin_compat
#print axioms SelectedInfinityScaling318.affine_overlap
