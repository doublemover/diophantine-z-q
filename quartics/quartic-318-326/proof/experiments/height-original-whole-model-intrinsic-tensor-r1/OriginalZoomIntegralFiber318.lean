module
public import IntegralZoomTensorFiber318
public import OriginalAllPrimeIntegralBicanonical318
public section
noncomputable section
namespace OriginalZoomIntegralFiber318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)
abbrev a := OriginalAllPrimeIntegralBicanonical318.contacts c t w
abbrev mode := OriginalAllPrimeIntegralBicanonical318.mode m
@[expose] def b0 : V c t w := (ContactScaledBicanonicalPoint318.J : V c t w)^2*
  IntegralZoomPointCoefficient318.fiber0 I.coordinate D.coefficients (a c t w) (mode (m:=m))
@[expose] def b1 : V c t w := (ContactScaledBicanonicalPoint318.J : V c t w)^2*
  IntegralZoomPointCoefficient318.fiber1 I.coordinate D.coefficients (a c t w) (mode (m:=m))

/-- The coefficient is the actual fiber of the already constructed
integral tensor section in its actual etale coordinate frame. -/
theorem tensor_fiber0 : IntegralZoomTensorFiber318.tensorFiber D.coefficients (a c t w) I.coordinate
    (mode (m:=m)) (ContactScaledBicanonicalPoint318.J^2 •
      OriginalAllPrimeIntegralBicanonical318.integralSection0 c t w D I)=b0 c t w D I := by
  rw [map_nsmul]
  change ContactScaledBicanonicalPoint318.J^2 •
    IntegralZoomTensorFiber318.tensorFiber _ _ _ _ (IntegralContactZoomCoefficients318.section0 _ _ _ _)=_
  rw [IntegralZoomTensorFiber318.tensorFiber_section0]
  simp only [b0,nsmul_eq_mul,Nat.cast_pow]

theorem tensor_fiber1 : IntegralZoomTensorFiber318.tensorFiber D.coefficients (a c t w) I.coordinate
    (mode (m:=m)) (ContactScaledBicanonicalPoint318.J^2 •
      OriginalAllPrimeIntegralBicanonical318.integralSection1 c t w D I)=b1 c t w D I := by
  rw [map_nsmul]
  change ContactScaledBicanonicalPoint318.J^2 •
    IntegralZoomTensorFiber318.tensorFiber _ _ _ _ (IntegralContactZoomCoefficients318.section1 _ _ _ _)=_
  rw [IntegralZoomTensorFiber318.tensorFiber_section1]
  simp only [b1,nsmul_eq_mul,Nat.cast_pow]

theorem b0_ne : b0 c t w D I≠0 := by
  apply mul_ne_zero (pow_ne_zero _ (by norm_num [ContactScaledBicanonicalPoint318.J]))
  exact IntegralZoomPointCoefficient318.fiber0_ne I.coordinate D.coefficients (a c t w)
    (mode (m:=m)) I.root (OriginalAllPrimeIntegralBicanonical318.integral_root_equation c t w D I) I.root_ne

theorem field_b0_ne : algebraMap (V c t w) (K c t) (b0 c t w D I)≠0 := by
  simpa only [map_zero] using (IsFractionRing.injective (V c t w) (K c t)).ne (b0_ne c t w D I)

/-- The finite and reciprocal integral fibers give the SAME original
field coordinate ratio, including when that coordinate is not integral. -/
theorem field_ratio : algebraMap (V c t w) (K c t) (b1 c t w D I)=
    (t : K c t)*algebraMap (V c t w) (K c t) (b0 c t w D I) := by
  cases m with
  | finite =>
      have h := IntegralZoomPointCoefficient318.finite_fiber1 I.coordinate D.coefficients (a c t w)
      have hi : b1 c t w D I=I.coordinate*b0 c t w D I := by
        unfold b0 b1
        rw [h]
        ring
      rw [hi,map_mul,I.coordinate_value]
      rfl
  | reciprocal =>
      have hr := IntegralZoomPointCoefficient318.reciprocal_ratio I.coordinate D.coefficients (a c t w)
      have hi : I.coordinate*b1 c t w D I=b0 c t w D I := by
        unfold b0 b1
        calc
          _ = (ContactScaledBicanonicalPoint318.J : V c t w)^2*
            (I.coordinate*IntegralZoomPointCoefficient318.fiber1 I.coordinate D.coefficients (a c t w) .reciprocal) := by ring
          _ = _ := by rw [hr]
      have hn : I.coordinate≠0 := IntegralZoomPointCoefficient318.reciprocal_coordinate_ne
        I.coordinate D.coefficients (a c t w) I.root I.root_ne
        (OriginalAllPrimeIntegralBicanonical318.integral_root_equation c t w D I)
      have hmap : algebraMap (V c t w) (K c t) I.coordinate≠0 := by
        simpa only [map_zero] using (IsFractionRing.injective (V c t w) (K c t)).ne hn
      have ht : (t : K c t)≠0 := by
        rw [I.coordinate_value] at hmap
        exact inv_ne_zero_iff.mp hmap
      have he := congrArg (algebraMap (V c t w) (K c t)) hi
      rw [map_mul,I.coordinate_value] at he
      change (t : K c t)⁻¹*algebraMap (V c t w) (K c t) (b1 c t w D I)=_ at he
      calc
        _ = (t : K c t)*((t : K c t)⁻¹*algebraMap (V c t w) (K c t) (b1 c t w D I)) := by rw [←mul_assoc,mul_inv_cancel₀ ht,one_mul]
        _ = _ := by rw [he]
end OriginalZoomIntegralFiber318
