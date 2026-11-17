module
public import ActualTwoDescentAllBadProducer318
public section
noncomputable section
namespace ActualTwoDescentTorsionTranslation318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]

def translatedX (n x : K) : K := -3*n*(x-n)/(x+3*n)
def translatedY (n x y : K) : K := -12*n^2*y/(x+3*n)^2

lemma translated_first (n x : K) (hA : x+3*n ≠ 0) :
    translatedX n x+3*n=12*n^2/(x+3*n) := by
  dsimp [translatedX]
  field_simp [hA]
  <;> ring

lemma translated_second (n x : K) (hA : x+3*n ≠ 0) :
    translatedX n x-n= -4*n*x/(x+3*n) := by
  dsimp [translatedX]
  field_simp [hA]
  <;> ring

/-- Explicit translation by the retained rational two-torsion point
(-3n,0), proved directly on the original cubic over any characteristic-zero
field. This is a genuine point map, not only an operation on signatures. -/
theorem translated_curve (n x y : K) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    (translatedY n x y)^2=translatedX n x*(translatedX n x-n)*(translatedX n x+3*n) := by
  calc
    (translatedY n x y)^2=144*n^4*y^2/(x+3*n)^4 := by
      dsimp [translatedY]
      field_simp [hA]
      <;> ring
    _=144*n^4*(x*(x-n)*(x+3*n))/(x+3*n)^4 := by rw [hc]
    _=translatedX n x*(translatedX n x-n)*(translatedX n x+3*n) := by
      rw [translated_first n x hA,translated_second n x hA]
      dsimp [translatedX]
      field_simp [hA]
      <;> ring

lemma translated_nonzero (n x : K) (hn : n ≠ 0) (hx : x ≠ 0)
    (hB : x-n ≠ 0) (hA : x+3*n ≠ 0) :
    translatedX n x ≠ 0 ∧ translatedX n x-n ≠ 0 ∧ translatedX n x+3*n ≠ 0 := by
  refine ⟨?_,?_,?_⟩
  · exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hB) hA
  · rw [translated_second n x hA]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hn) hx) hA
  · rw [translated_first n x hA]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hn)) hA

/-- The first translated Kummer coordinate is the original first one
multiplied by3 and by the displayed nonzero square. -/
lemma translated_first_square (n x : K) (hA : x+3*n ≠ 0) :
    translatedX n x+3*n=(3*(x+3*n))*(2*n/(x+3*n))^2 := by
  rw [translated_first n x hA]
  field_simp [hA]
  <;> ring

/-- The second translated coordinate is the original second one multiplied
by -n and by an explicit square, using the ACTUAL original cubic equation. -/
lemma translated_second_square (n x y : K) (hB : x-n ≠ 0) (hA : x+3*n ≠ 0)
    (hc : y^2=x*(x-n)*(x+3*n)) :
    translatedX n x-n=((-n)*(x-n))*(2*y/((x-n)*(x+3*n)))^2 := by
  rw [translated_second n x hA,div_pow,mul_pow,hc]
  field_simp [hA,hB]
  <;> ring

end ActualTwoDescentTorsionTranslation318
