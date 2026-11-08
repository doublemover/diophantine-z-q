module
public import FifthBranchLocal318
public import WeierstrassGluing318
public section
noncomputable section
namespace FifthBranchOverlap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FifthCharacterShortPolynomial318 FifthBranchEquation318 FifthBranchLocal318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
section Generic
variable {S:Type*} [CommRing S]
variable (m k w u v x y:S) (n h t:Sˣ)
variable (hw:w^2=(t:S)*(h:S))
variable (hu:u*↑(n*h)=(m+k*(t:S))*w) (hv:v*↑(n*h)=(t:S)*w)
variable (hx:x*(t:S)=m+k*(t:S)) (hy:y*(t:S)^2=(n:S)*w)
include hw hu hx hy in
theorem output_x : u*y=x:=by
  apply (Units.mul_right_inj (n*h*t^2)).mp
  change (↑(n*h*t^2):S)*(u*y)=(↑(n*h*t^2):S)*x
  calc
    _=(u*↑(n*h))*(y*(t:S)^2):=by simp only [Units.val_mul,Units.val_pow_eq_pow_val];ring
    _=((m+k*(t:S))*w)*((n:S)*w):=by rw [hu,hy]
    _=(n:S)*(m+k*(t:S))*w^2:=by ring
    _=(↑(n*h*t^2):S)*x:=by rw [hw,←hx];simp only [Units.val_mul,Units.val_pow_eq_pow_val];ring
include hw hv hy in
theorem output_y : v*y=1:=by
  apply (Units.mul_right_inj (n*h*t^2)).mp
  change (↑(n*h*t^2):S)*(v*y)=(↑(n*h*t^2):S)*1
  calc
    _=(v*↑(n*h))*(y*(t:S)^2):=by simp only [Units.val_mul,Units.val_pow_eq_pow_val];ring
    _=((t:S)*w)*((n:S)*w):=by rw [hv,hy]
    _=(n:S)*(t:S)*w^2:=by ring
    _=(↑(n*h*t^2):S)*1:=by rw [hw];simp only [Units.val_mul,Units.val_pow_eq_pow_val];ring
end Generic
end FifthBranchOverlap318
