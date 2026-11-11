module
public import IntegralContactZoomCoefficients318
public section
noncomputable section
namespace IntegralZoomPointCoefficient318
open IntegralContactZoomCoefficients318
set_option maxHeartbeats 1400000
variable {V : Type*} [CommRing V] (α β γ : Fin 4 → V) (t : V)
abbrev point := IntegralZoomNeighborhood318.point V α β γ t

theorem productUnit_point : point α β γ t
    (IntegralZoomProductUnits318.productUnit α β γ t : IntegralZoomNeighborhood318.Chart V α β γ t)=1 := by
  rw [IntegralZoomProductUnits318.productUnit_val,map_prod]
  simp only [map_add,map_one,map_mul,map_ofNat,IntegralZoomNeighborhood318.point_generator,
    mul_zero,add_zero,Finset.prod_const_one]

theorem productUnit_inverse_point : point α β γ t
    (↑(IntegralZoomProductUnits318.productUnit α β γ t)⁻¹ : IntegralZoomNeighborhood318.Chart V α β γ t)=1 := by
  have h := congrArg (point α β γ t)
    (Units.mul_inv (IntegralZoomProductUnits318.productUnit α β γ t))
  simpa only [map_mul,map_one,productUnit_point,one_mul] using h

theorem common_point (d : Fin 4 → V) : point α β γ t
    (IntegralZoomProductUnits318.commonCoefficient α β γ t d)=
      16*(∏ i : Fin 4,d i)*IntegralQuadraticPointZoom318.product α β γ t := by
  simp only [IntegralZoomProductUnits318.commonCoefficient,map_mul,map_ofNat,map_pow,
    IntegralZoomNeighborhood318.point_scalar,productUnit_inverse_point,one_pow,mul_one]

variable (d a : Fin 4 → V) (m : Mode)
abbrev actualPoint := point (alpha d a m) d (gamma d a m) t
@[expose] def fiber0 : V := actualPoint t d a m (q0 d a t m)
@[expose] def fiber1 : V := actualPoint t d a m (q1 d a t m)
@[expose] def commonValue : V :=
  16*(∏ i : Fin 4,d i)*IntegralQuadraticPointZoom318.product (alpha d a m) d (gamma d a m) t

theorem finite_fiber0 : fiber0 t d a .finite=commonValue t d a .finite := by
  simp only [fiber0,q0,weight,map_mul,map_one,mul_one,commonCoefficient,common_point,commonValue]
theorem finite_fiber1 : fiber1 t d a .finite=t*fiber0 t d a .finite := by
  simp only [fiber1,q1,map_mul,IntegralZoomNeighborhood318.point_oldCoordinate,fiber0]
theorem reciprocal_fiber0 : fiber0 t d a .reciprocal=commonValue t d a .reciprocal*t^4 := by
  simp only [fiber0,q0,weight,map_mul,map_pow,commonCoefficient,common_point,
    IntegralZoomNeighborhood318.point_oldCoordinate,commonValue]
theorem reciprocal_fiber1 : fiber1 t d a .reciprocal=commonValue t d a .reciprocal*t^3 := by
  simp only [fiber1,q1,map_mul,map_pow,commonCoefficient,common_point,
    IntegralZoomNeighborhood318.point_oldCoordinate,commonValue]
theorem reciprocal_ratio : t*fiber1 t d a .reciprocal=fiber0 t d a .reciprocal := by
  rw [reciprocal_fiber0,reciprocal_fiber1]
  ring

variable [IsDomain V] [CharZero V]
  (y : Fin 4 → V)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
  (hn : ∀ i,y i≠0)

include hy hn in
theorem value_ne (i : Fin 4) : IntegralQuadraticPointZoom318.value
    (alpha d a m) d (gamma d a m) t i≠0 := by
  rw [←hy i]
  exact pow_ne_zero _ (hn i)

include hy hn in
theorem coefficient_ne (i : Fin 4) : d i≠0 := by
  intro h
  apply value_ne t d a m y hy hn i
  cases m <;> simp [IntegralQuadraticPointZoom318.value,alpha,gamma,h]

include hy hn in
theorem commonValue_ne : commonValue t d a m≠0 := by
  unfold commonValue IntegralQuadraticPointZoom318.product
  apply mul_ne_zero
  · exact mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.mpr (fun i _ => coefficient_ne t d a m y hy hn i))
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => value_ne t d a m y hy hn i)

include hn in
theorem reciprocal_coordinate_ne
    (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value
      (alpha d a .reciprocal) d (gamma d a .reciprocal) t i) : t≠0 := by
  intro h
  apply value_ne t d a .reciprocal y hy hn 0
  simp [IntegralQuadraticPointZoom318.value,h,gamma]

include hy hn in
theorem fiber0_ne : fiber0 t d a m≠0 := by
  cases m with
  | finite => rw [finite_fiber0]; exact commonValue_ne t d a .finite y hy hn
  | reciprocal =>
      rw [reciprocal_fiber0]
      exact mul_ne_zero (commonValue_ne t d a .reciprocal y hy hn)
        (pow_ne_zero _ (reciprocal_coordinate_ne t d a y hn hy))
end IntegralZoomPointCoefficient318
