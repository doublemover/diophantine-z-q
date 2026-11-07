module
public import TangentOpenAlgebra318
public section
noncomputable section
namespace HomogeneousAddition318
set_option maxHeartbeats 500000
variable {R:Type*} [CommRing R]

/-- Homogeneous addition identity, valid over every commutative ring without any cancelled
coordinate denominator. -/
theorem numerator_identity (a b X1 Y1 X2 Y2 d e:R) :
    let U:=e^2-(X1+X2)*d^2
    let V:=e*(X1*d^2-U)-Y1*d^3
    V^2-U^3-a*U*d^4-b*d^6 = d^6*(Y1^2-X1^3-a*X1-b)+
      (U-X1*d^2)*d^2*(d*(e*(Y1+Y2)-d*(X1^2+X1*X2+X2^2+a))+
        e*(e*(X2-X1)-d*(Y2-Y1))) := by
  dsimp
  ring

/-- Actual input equations annihilate the ordinary-chord homogeneous numerator. -/
theorem chord_numerator (a b X1 Y1 X2 Y2:R)
    (h1:Y1^2-X1^3-a*X1-b=0) (h2:Y2^2-X2^3-a*X2-b=0) :
    let d:=X2-X1
    let e:=Y2-Y1
    let U:=e^2-(X1+X2)*d^2
    let V:=e*(X1*d^2-U)-Y1*d^3
    V^2-U^3-a*U*d^4-b*d^6=0 := by
  have hs : (Y2-Y1)*(Y1+Y2)-(X2-X1)*(X1^2+X1*X2+X2^2+a)=0 := by
    linear_combination h2-h1
  have hh:=numerator_identity a b X1 Y1 X2 Y2 (X2-X1) (Y2-Y1)
  dsimp only at hh ⊢
  rw [h1,hs] at hh
  linear_combination hh

/-- The tangent/secant numerator also vanishes, including at 2-torsion doubling. -/
theorem tangent_numerator (a b X1 Y1 X2 Y2:R)
    (h1:Y1^2-X1^3-a*X1-b=0) (h2:Y2^2-X2^3-a*X2-b=0) :
    let d:=Y1+Y2
    let e:=X1^2+X1*X2+X2^2+a
    let U:=e^2-(X1+X2)*d^2
    let V:=e*(X1*d^2-U)-Y1*d^3
    V^2-U^3-a*U*d^4-b*d^6=0 := by
  have hs : (X1^2+X1*X2+X2^2+a)*(X2-X1)-(Y1+Y2)*(Y2-Y1)=0 := by
    linear_combination h1-h2
  have hh:=numerator_identity a b X1 Y1 X2 Y2 (Y1+Y2) (X1^2+X1*X2+X2^2+a)
  dsimp only at hh ⊢
  rw [h1,hs] at hh
  have hz : (X1^2+X1*X2+X2^2+a)*(Y1+Y2)-(Y1+Y2)*(X1^2+X1*X2+X2^2+a)=0 := by ring
  rw [hz] at hh
  simpa only [mul_zero,add_zero,zero_add] using hh

/-- Dehomogenizing at the genuine Y numerator yields the infinity chart equation. -/
theorem infinity_equation (a b U V d k:R)
    (h:V^2-U^3-a*U*d^4-b*d^6=0) (hk:V*k=1) :
    d^3*k-(U*d*k)^3-a*(U*d*k)*(d^3*k)^2-b*(d^3*k)^3=0 := by
  calc
    _ = d^3*k^3*(V^2-U^3-a*U*d^4-b*d^6)+d^3*k*(1-(V*k)^2) := by ring
    _ = 0 := by rw [h,hk]; ring

end HomogeneousAddition318
