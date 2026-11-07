module
public import QuarticOptimization
public section
namespace CoupledExponents

variable {K : Type*} [Field K]

theorem coupled_weights (e q x y T V : K) (he : e ≠ 0) (hq : q ≠ 0)
    (hT : x*T = q^2) (hy : y*T = e^12*x^2)
    (hV : V*e^12 = e^3*x^2) (hfinal : V^2 = q^3*y) :
    x = q*e^30 ∧ y = q*e^102 := by
  have hx : x ≠ 0 := by
    intro hx
    have hz : q^2 = 0 := by simpa [hx] using hT.symm
    exact (pow_ne_zero 2 hq) hz
  have hy' : y*q^2 = e^12*x^3 := by
    linear_combination x*hy-y*hT
  have hBig : e^6*x^4 = q*e^36*x^3 := by
    calc
      e^6*x^4 = (V*e^12)^2 := by rw [hV]; ring
      _ = V^2*e^24 := by ring
      _ = (q^3*y)*e^24 := by rw [hfinal]
      _ = q*e^24*(y*q^2) := by ring
      _ = q*e^24*(e^12*x^3) := by rw [hy']
      _ = q*e^36*x^3 := by ring
  have hz : e^6*x^3*(x-q*e^30) = 0 := by
    linear_combination hBig
  have hx' : x = q*e^30 := sub_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_left (mul_ne_zero (pow_ne_zero 6 he) (pow_ne_zero 3 hx)))
  refine ⟨hx', ?_⟩
  apply mul_right_cancel₀ (pow_ne_zero 2 hq)
  calc
    y*q^2 = e^12*x^3 := hy'
    _ = (q*e^102)*q^2 := by rw [hx']; ring

theorem coupled_weights_converse (e q : K) (he : e ≠ 0) :
    let x := q*e^30
    let y := q*e^102
    let T := q/e^30
    let V := q^2*e^51
    x*T = q^2 ∧ y*T = e^12*x^2 ∧ V*e^12 = e^3*x^2 ∧ V^2 = q^3*y := by
  dsimp
  constructor
  · field_simp [he]
  constructor
  · field_simp [he] <;> ring
  constructor <;> ring

end CoupledExponents
