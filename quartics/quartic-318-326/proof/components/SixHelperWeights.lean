module
public import QuarticOptimization
public section
namespace SixHelperWeights
variable {K : Type*} [Field K]

theorem outputs (e q d a b c T x y : K) (he : e ≠ 0)
    (hea : e*a=1) (hab : a*b=e^2) (hac : a*c=b^2)
    (hqd : q*d=e) (hcT : c*T=d) (hxT : x*T=c^2)
    (hy : q^3*y=(x^2)^2) : x=q*e^20 ∧ y=q*e^80 := by
  have hq : q ≠ 0 := by intro hz; rw [hz,zero_mul] at hqd; exact he hqd.symm
  have hb : b=e^3 := by
    calc
      b=(e*a)*b := by rw [hea]; simp
      _=e*(a*b) := by ring
      _=e^3 := by rw [hab]; ring
  have hc : c=e^7 := by
    calc
      c=(e*a)*c := by rw [hea]; simp
      _=e*(a*c) := by ring
      _=e^7 := by rw [hac,hb]; ring
  have hprod : e*x=q*e^21 := by
    calc
      e*x=(q*d)*x := by rw [hqd]
      _=q*c*(x*T) := by rw [←hcT]; ring
      _=q*e^21 := by rw [hxT,hc]; ring
  have hx0 : e*(x-q*e^20)=0 := by linear_combination hprod
  have hx : x=q*e^20 := sub_eq_zero.mp ((mul_eq_zero.mp hx0).resolve_left he)
  refine ⟨hx, ?_⟩
  rw [hx] at hy
  have hy0 : q^3*(y-q*e^80)=0 := by linear_combination hy
  exact sub_eq_zero.mp ((mul_eq_zero.mp hy0).resolve_left (pow_ne_zero 3 hq))

theorem reconstruction (e q d : K) (he : e ≠ 0) (hqd : q*d=e) :
    e*(1/e)=1 ∧ (1/e)*e^3=e^2 ∧ (1/e)*e^7=(e^3)^2 ∧
      e^7*(d/e^7)=d ∧ (q*e^20)*(d/e^7)=(e^7)^2 ∧
      q^3*(q*e^80)=((q*e^20)^2)^2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp [he]
  · field_simp [he]
  · field_simp [he]
  · field_simp [he]
  · field_simp [he]
    exact hqd
  · ring

end SixHelperWeights
