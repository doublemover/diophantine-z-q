module
public import ActualPrescribedLocalVolume318
public section
noncomputable section
namespace ActualQuadricScaling318
open QuadricCRTAssembly318 ActualQuadricTaylor318 ActualOriginalModularLift318
open ActualCoordinateLiftFiber318
set_option maxHeartbeats 22000000

lemma original_homogeneity {R : Type*} [CommRing R] (κ r : R) (x : Coordinates R) :
    equation κ (translate ((0,0),(0,0),0) x r)=r^2*equation κ x := by
  simp only [equation,translate]
  ring
lemma digits_zero (m : ℕ) : digits m (((0,0),(0,0),0):Coordinates (ZMod m))=((0,0),(0,0),0) := by
  simp only [digits,ZMod.val_zero,Nat.cast_zero]

/-- Literal integer representatives followed by reduction give the
same original coefficient-wise map as the ambient ring homomorphism. -/
lemma reduce_integer_digits (m p : ℕ) [NeZero m] [NeZero p]
    (z : Coordinates (ZMod (m*p))) :
    mapCoordinates (ActualResidueDigitEquiv318.reduce m p) z=
      mapCoordinates (Int.castRingHom (ZMod m)) (digits (m*p) z) := by
  simp only [mapCoordinates,digits,Int.castRingHom_apply,Int.cast_natCast]
  exact Prod.ext
    (Prod.ext (ActualResidueDigitEquiv318.actual_base_component m p z.1.1).symm
      (ActualResidueDigitEquiv318.actual_base_component m p z.1.2).symm)
    (Prod.ext
      (Prod.ext (ActualResidueDigitEquiv318.actual_base_component m p z.2.1.1).symm
        (ActualResidueDigitEquiv318.actual_base_component m p z.2.1.2).symm)
      (ActualResidueDigitEquiv318.actual_base_component m p z.2.2).symm)

/-- Scaling all FIVE original coordinates by p loses exactly p^2
from the original quadratic equation, not p or a shifted form. -/
theorem actual_singular_test (κ : ℤ) (m p : ℕ) [NeZero m] [NeZero p]
    (z : Coordinates (ZMod (m*p))) :
    equation (κ:ZMod (p*(m*p)))
      (coordinateFiberEquiv p (m*p) ((0,0),(0,0),0) z).1=0 ↔
    equation (κ:ZMod m) (mapCoordinates (ActualResidueDigitEquiv318.reduce m p) z)=0 := by
  have hp0 : (p:ℤ)≠0 := by exact_mod_cast NeZero.ne p
  rw [actual_integer_lift_formula,digits_zero]
  rw [equation_map,original_homogeneity]
  rw [reduce_integer_digits,equation_map]
  simp only [Int.castRingHom_apply,ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_mul]
  have hm : (p:ℤ)*((m:ℤ)*p)=(p:ℤ)^2*m := by ring
  rw [hm,mul_dvd_mul_iff_left (pow_ne_zero 2 hp0)]

end ActualQuadricScaling318
