module
public import ActualTwoDescentHalvingRoots318
public section
noncomputable section
namespace ActualTwoDescentHalvingCoordinates318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


def halfX (x a b c : K) : K := x+a*b+a*c+b*c
def halfY (a b c : K) : K := -(a+b)*(a+c)*(b+c)
def halfSlope (a b c : K) : K := -(a+b+c)

lemma half_factors (n x a b c : K) (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    halfX x a b c=(a+b)*(a+c) ∧
    halfX x a b c-n=(a+b)*(b+c) ∧
    halfX x a b c+3*n=(a+c)*(b+c) := by
  dsimp [halfX]
  exact ⟨by linear_combination -ha, by linear_combination -hb, by linear_combination -hc⟩

lemma half_curve (n x a b c : K) (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    (halfY a b c)^2=halfX x a b c*(halfX x a b c-n)*(halfX x a b c+3*n) := by
  obtain ⟨h1,h2,h3⟩ := half_factors n x a b c ha hb hc
  rw [h2,h3,h1]
  dsimp [halfY]
  ring

lemma half_sum_nonzero (n x a b c : K) (hn : n ≠ 0)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    a+b ≠ 0 ∧ a+c ≠ 0 ∧ b+c ≠ 0 := by
  constructor
  · intro he
    apply hn
    linear_combination ha-hb-(a-b)*he
  constructor
  · intro he
    apply hn
    linear_combination (hc-ha+(a-c)*he)/3
  · intro he
    apply hn
    linear_combination (hc-hb+(b-c)*he)/4

lemma half_y_nonzero (n x a b c : K) (hn : n ≠ 0)
    (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) : halfY a b c ≠ 0 := by
  obtain ⟨h1,h2,h3⟩ := half_sum_nonzero n x a b c hn ha hb hc
  exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h1) h2) h3

lemma half_tangent (n x a b c : K) (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    2*halfY a b c*halfSlope a b c = 3*(halfX x a b c)^2+4*n*halfX x a b c-3*n^2 := by
  dsimp [halfX,halfY,halfSlope]
  linear_combination
    (b+c)*(2*a+b+c)*ha +
    (2*a*b+2*a*c+2*b*c+c^2+x)*hb +
    (2*a*b+2*a*c+2*b*c-n+2*x)*hc

lemma half_double_x (n x a b c : K) (ha : a^2=x) (hb : b^2=x-n) (hc : c^2=x+3*n) :
    (halfSlope a b c)^2-2*n-2*halfX x a b c=x := by
  dsimp [halfX,halfSlope]
  linear_combination ha+hb+hc

lemma half_double_y (x y a b c : K) (hprod : a*b*c= -y) :
    halfSlope a b c*(halfX x a b c-x)-halfY a b c=y := by
  dsimp [halfSlope,halfX,halfY]
  linear_combination -hprod

end ActualTwoDescentHalvingCoordinates318
