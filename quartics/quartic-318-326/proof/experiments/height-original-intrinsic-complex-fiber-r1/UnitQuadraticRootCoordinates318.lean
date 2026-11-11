module
public import Mathlib.Tactic
public section
noncomputable section
namespace UnitQuadraticRootCoordinates318
variable {A : Type*} [CommRing A] (two p : Aˣ) (htwo : (two : A)=2)
@[expose] def inverseCoordinate (y : A) : A := (↑two⁻¹ : A)*((↑p⁻¹ : A)*y-1)

theorem twice_coordinate (y : A) :
    2*inverseCoordinate two p y+1=(↑p⁻¹ : A)*y := by
  have htwoInv : (2 : A)*(↑two⁻¹ : A)=1 := by rw [←htwo,Units.mul_inv]
  unfold inverseCoordinate
  linear_combination ((↑p⁻¹ : A)*y-1)*htwoInv

theorem recover_original (y : A) : p*(1+2*inverseCoordinate two p y)=y := by
  rw [add_comm (1 : A),twice_coordinate two p htwo]
  rw [←mul_assoc,Units.mul_inv,one_mul]

theorem recover_new (z : A) : inverseCoordinate two p ((p : A)*(1+2*z))=z := by
  unfold inverseCoordinate
  rw [←mul_assoc,Units.inv_mul,one_mul,add_sub_cancel_left]
  have htwoInv : (↑two⁻¹ : A)*(2 : A)=1 := by rw [←htwo,Units.inv_mul]
  rw [←mul_assoc,htwoInv,one_mul]

theorem quadratic_relation (y q : A)
    (hy : y^2=(p : A)^2*(1+4*q)) :
    (inverseCoordinate two p y)^2+inverseCoordinate two p y=q := by
  let z := inverseCoordinate two p y
  have hyr : y=(p : A)*(1+2*z) := (recover_original two p htwo y).symm
  rw [hyr] at hy
  have hs : ((2 : A)*(p : A))^2*(z^2+z-q)=0 := by linear_combination hy
  let U : Aˣ := (two*p)^2
  have hU : (U : A)=((2 : A)*(p : A))^2 := by
    change ((two : A)*(p : A))^2=_
    rw [htwo]
  have hc := congrArg (fun r : A => (↑U⁻¹ : A)*r) hs
  rw [←hU,←mul_assoc,Units.inv_mul,one_mul,mul_zero] at hc
  exact sub_eq_zero.mp hc

theorem derivative_unit (y : A) (hy : IsUnit y) :
    IsUnit (2*inverseCoordinate two p y+1) := by
  rw [twice_coordinate two p htwo]
  exact p⁻¹.isUnit.mul hy
end UnitQuadraticRootCoordinates318
