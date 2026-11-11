module
public import ActualTwoDescentHalfFlipProducts318
public section
noncomputable section
namespace ActualTwoDescentHalfFlipOrdinates318
set_option maxHeartbeats 16000000

open ActualTwoDescentHalvingCoordinates318 ActualTwoDescentHalfFlipProducts318
variable {K : Type*} [Field K] [CharZero K]

lemma actual_half_flip_zero_ordinate (n x a b c : K)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    halfY a (-b) (-c)*(halfX x a b c)^2=3*n^2*halfY a b c := by
  have hp := actual_half_flip_zero_product n x a b c ha hb hc
  have hy : halfY a (-b) (-c)=(b+c)*halfX x a (-b) (-c) := by
    rw [(half_factors n x a (-b) (-c) ha (by simpa using hb) (by simpa using hc)).1]
    dsimp [halfY]; ring
  have hy0 : halfY a b c= -(b+c)*halfX x a b c := by
    rw [(half_factors n x a b c ha hb hc).1]
    dsimp [halfY]; ring
  rw [hy,hy0]
  linear_combination (b+c)*halfX x a b c*hp

lemma actual_half_flip_first_ordinate (n x a b c : K)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    halfY (-a) b (-c)*(halfX x a b c-n)^2= -4*n^2*halfY a b c := by
  have hp := actual_half_flip_first_product n x a b c ha hb hc
  have hy : halfY (-a) b (-c)=(a+c)*(halfX x (-a) b (-c)-n) := by
    rw [(half_factors n x (-a) b (-c) (by simpa using ha) hb (by simpa using hc)).2.1]
    dsimp [halfY]; ring
  have hy0 : halfY a b c= -(a+c)*(halfX x a b c-n) := by
    rw [(half_factors n x a b c ha hb hc).2.1]
    dsimp [halfY]; ring
  rw [hy,hy0]
  linear_combination (a+c)*(halfX x a b c-n)*hp

lemma actual_half_flip_last_ordinate (n x a b c : K)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    halfY (-a) (-b) c*(halfX x a b c+3*n)^2= -12*n^2*halfY a b c := by
  have hp := actual_half_flip_last_product n x a b c ha hb hc
  have hy : halfY (-a) (-b) c=(a+b)*(halfX x (-a) (-b) c+3*n) := by
    rw [(half_factors n x (-a) (-b) c (by simpa using ha) (by simpa using hb) hc).2.2]
    dsimp [halfY]; ring
  have hy0 : halfY a b c= -(a+b)*(halfX x a b c+3*n) := by
    rw [(half_factors n x a b c ha hb hc).2.2]
    dsimp [halfY]; ring
  rw [hy,hy0]
  linear_combination (a+b)*(halfX x a b c+3*n)*hp

end ActualTwoDescentHalfFlipOrdinates318
