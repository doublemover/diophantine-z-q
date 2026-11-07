module
public import QuarticOptimization
public section
namespace Height925DeltaLog
set_option maxRecDepth 100000
set_option maxHeartbeats 0

@[expose] def H1 (x : ℚ) : ℚ := (1)*x^0 + ((1/10 : ℚ))*x^1

@[expose] def J1 (x : ℚ) : ℚ := (1)*x^0 + ((-1/5 : ℚ))*x^1

@[expose] def R1 (x : ℚ) : ℚ := ((-1/10 : ℚ))*x^0

@[expose] def dJ1 (x : ℚ) : ℚ := ((-1/5 : ℚ))*x^0

theorem composition1 (x : ℚ) : H1 (-2*x-x^2) = J1 x+x^2*R1 x := by
  unfold H1 J1 R1
  ring

theorem differential1 (x : ℚ) : (1+x)*J1 x+2*x*(2+x)*dJ1 x-1 = (-3/5 : ℚ)*x^2 := by
  unfold J1 dJ1
  ring

@[expose] def H4 (x : ℚ) : ℚ := (1)*x^0 + ((1/10 : ℚ))*x^1 + ((1/24 : ℚ))*x^2 + ((5/208 : ℚ))*x^3 + ((35/2176 : ℚ))*x^4

@[expose] def J4 (x : ℚ) : ℚ := (1)*x^0 + ((-1/5 : ℚ))*x^1 + ((1/15 : ℚ))*x^2 + ((-1/39 : ℚ))*x^3 + ((7/663 : ℚ))*x^4

@[expose] def R4 (x : ℚ) : ℚ := ((655/1768 : ℚ))*x^0 + ((80/221 : ℚ))*x^1 + ((35/272 : ℚ))*x^2 + ((35/2176 : ℚ))*x^3

@[expose] def dJ4 (x : ℚ) : ℚ := ((-1/5 : ℚ))*x^0 + ((2/15 : ℚ))*x^1 + ((-1/13 : ℚ))*x^2 + ((28/663 : ℚ))*x^3

theorem composition4 (x : ℚ) : H4 (-2*x-x^2) = J4 x+x^5*R4 x := by
  unfold H4 J4 R4
  ring

theorem differential4 (x : ℚ) : (1+x)*J4 x+2*x*(2+x)*dJ4 x-1 = (21/221 : ℚ)*x^5 := by
  unfold J4 dJ4
  ring

theorem delta_square_identity (v w : ℚ) :
    (v-1)^2-(2-2*v-w)=v^2+w-1 := by ring

theorem delta_square_of_curve (v w : ℚ) (h : v^2+w=1) :
    (v-1)^2=2-2*v-w := by nlinarith

end Height925DeltaLog
