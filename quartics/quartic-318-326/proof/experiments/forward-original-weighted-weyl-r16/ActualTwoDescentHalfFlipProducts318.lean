module
public import ActualTwoDescentGeneralRootTranslation318
public section
noncomputable section
namespace ActualTwoDescentHalfFlipProducts318
set_option maxHeartbeats 16000000

open ActualTwoDescentHalvingCoordinates318
variable {K : Type*} [Field K] [CharZero K]

lemma actual_half_flip_zero_product (n x a b c : K)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    halfX x a b c*halfX x a (-b) (-c)= -3*n^2 := by
  rw [(half_factors n x a b c ha hb hc).1,
    (half_factors n x a (-b) (-c) ha (by simpa using hb) (by simpa using hc)).1]
  calc
    _=(a^2-b^2)*(a^2-c^2) := by ring
    _= -3*n^2 := by rw [ha,hb,hc]; ring

lemma actual_half_flip_first_product (n x a b c : K)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    (halfX x a b c-n)*(halfX x (-a) b (-c)-n)=4*n^2 := by
  rw [(half_factors n x a b c ha hb hc).2.1,
    (half_factors n x (-a) b (-c) (by simpa using ha) hb (by simpa using hc)).2.1]
  calc
    _=(b^2-a^2)*(b^2-c^2) := by ring
    _=4*n^2 := by rw [ha,hb,hc]; ring

lemma actual_half_flip_last_product (n x a b c : K)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    (halfX x a b c+3*n)*(halfX x (-a) (-b) c+3*n)=12*n^2 := by
  rw [(half_factors n x a b c ha hb hc).2.2,
    (half_factors n x (-a) (-b) c (by simpa using ha) (by simpa using hb) hc).2.2]
  calc
    _=(c^2-a^2)*(c^2-b^2) := by ring
    _=12*n^2 := by rw [ha,hb,hc]; ring

end ActualTwoDescentHalfFlipProducts318
