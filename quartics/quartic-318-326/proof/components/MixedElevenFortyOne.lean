module
public import QuarticOptimization
public section
namespace MixedElevenFortyOne
variable {K : Type*} [Field K]

theorem weights (e q e2 e4 e5 e10 e20 q11 q41 : K) (hq : q ≠ 0)
    (h2 : e2=e^2) (h4 : e4=e2^2) (h5 : e5=e4*e)
    (h10 : e10=e5^2) (h20 : e20=e10^2)
    (h11 : q11=q*e20) (h41 : q^3*q41=(q11^2)^2) :
    q11=q*e^20 ∧ q41=q*e^80 := by
  have h20' : e20=e^20 := by rw [h20,h10,h5,h4,h2]; ring
  have hp : q11=q*e^20 := by rw [h11,h20']
  refine ⟨hp, ?_⟩
  have hz : q^3*(q41-q*e^80)=0 := by
    rw [hp] at h41
    linear_combination h41
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (pow_ne_zero 3 hq))

theorem weight_converse (e q : K) :
    q^3*(q*e^80)=((q*e^20)^2)^2 := by ring

end MixedElevenFortyOne
