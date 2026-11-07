module
public import QuarticOptimization
public section
namespace Height13DeltaLog
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

@[expose] def H8 (x : ℚ) : ℚ := (1)*x^0 + ((1/10 : ℚ))*x^1 + ((1/24 : ℚ))*x^2 + ((5/208 : ℚ))*x^3 + ((35/2176 : ℚ))*x^4 + ((3/256 : ℚ))*x^5 + ((231/25600 : ℚ))*x^6 + ((429/59392 : ℚ))*x^7 + ((195/32768 : ℚ))*x^8

@[expose] def J8 (x : ℚ) : ℚ := (1)*x^0 + ((-1/5 : ℚ))*x^1 + ((1/15 : ℚ))*x^2 + ((-1/39 : ℚ))*x^3 + ((7/663 : ℚ))*x^4 + ((-1/221 : ℚ))*x^5 + ((11/5525 : ℚ))*x^6 + ((-11/12325 : ℚ))*x^7 + ((1/2465 : ℚ))*x^8

@[expose] def R8 (x : ℚ) : ℚ := ((47631/18560 : ℚ))*x^0 + ((132681/18560 : ℚ))*x^1 + ((405993/46400 : ℚ))*x^2 + ((2252187/371200 : ℚ))*x^3 + ((76167/29696 : ℚ))*x^4 + ((9789/14848 : ℚ))*x^5 + ((195/2048 : ℚ))*x^6 + ((195/32768 : ℚ))*x^7

@[expose] def dJ8 (x : ℚ) : ℚ := ((-1/5 : ℚ))*x^0 + ((2/15 : ℚ))*x^1 + ((-1/13 : ℚ))*x^2 + ((28/663 : ℚ))*x^3 + ((-5/221 : ℚ))*x^4 + ((66/5525 : ℚ))*x^5 + ((-77/12325 : ℚ))*x^6 + ((8/2465 : ℚ))*x^7

theorem composition8 (x : ℚ) : H8 (-2*x-x^2) = J8 x+x^9*R8 x := by
  unfold H8 J8 R8
  ring

theorem differential8 (x : ℚ) : (1+x)*J8 x+2*x*(2+x)*dJ8 x-1 = (1/145 : ℚ)*x^9 := by
  unfold J8 dJ8
  ring

theorem delta_square_identity (v w : ℚ) :
    (v-1)^2-(2-2*v-w)=v^2+w-1 := by ring

theorem delta_square_of_curve (v w : ℚ) (h : v^2+w=1) :
    (v-1)^2=2-2*v-w := by nlinarith

end Height13DeltaLog
