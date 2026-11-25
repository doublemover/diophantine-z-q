module
public import QuarticOptimization
public section
namespace DegenerateDetector
variable {K : Type*} [Field K]

theorem zero_parameter_iff (A t e : K) (F : K → K) (hA : A ≠ 0)
    (hF1 : F 1 ≠ 0) (heq : e*F t=(A*(t-1))^5) : e=0 ↔ t=1 := by
  constructor
  · intro he
    rw [he,zero_mul] at heq
    have hp : A*(t-1)=0 := (pow_eq_zero_iff (by decide : (5:ℕ) ≠ 0)).mp heq.symm
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hA)
  · intro ht
    rw [ht,sub_self,mul_zero,zero_pow (by decide)] at heq
    exact (mul_eq_zero.mp heq).resolve_right hF1

theorem nondegenerate_domains (A t e : K) (F : K → K) (hA : A ≠ 0)
    (hF1 : F 1 ≠ 0) (heq : e*F t=(A*(t-1))^5) (he : e ≠ 0) :
    t-1 ≠ 0 ∧ F t ≠ 0 := by
  have ht : t ≠ 1 := by
    intro ht
    exact he ((zero_parameter_iff A t e F hA hF1 heq).mpr ht)
  have hd : t-1 ≠ 0 := sub_ne_zero.mpr ht
  refine ⟨hd,?_⟩
  have hh : e*F t ≠ 0 := by rw [heq]; exact pow_ne_zero 5 (mul_ne_zero hA hd)
  exact (mul_ne_zero_iff.mp hh).2

theorem base_fused_equation (q e delta F : K)
    (he : q*delta^3=e) (hq : q*F=delta^2) : e*F=delta^5 := by
  calc
    e*F=(q*delta^3)*F := by rw [he]
    _=(q*F)*delta^3 := by ring
    _=delta^5 := by rw [hq]; ring

end DegenerateDetector
