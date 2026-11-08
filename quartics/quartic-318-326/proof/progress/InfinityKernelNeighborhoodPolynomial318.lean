module
public import InfinityVietaAlgebra318
public section
namespace InfinityKernelNeighborhoodPolynomial318
open InfinityVietaAlgebra318
set_option maxHeartbeats 600000
variable {R:Type*} [CommRing R]
@[expose] def Q (A B u v:R) := q A B u v v
@[expose] def S (A u v:R) := s A u u v
@[expose] def C (A B u v:R) := Q A B u v^3+A*S A u v^2*Q A B u v+B*S A u v^3
@[expose] def G (B v:R) := 1-B*v^2
@[expose] def K (A B u v:R) := 2*A*S A u v*Q A B u v+3*B*S A u v^2
@[expose] def H (A B u v:R) :=
  G B v*(3*C A B u v-K A B u v*S A u v)+K A B u v*Q A B u v*(u^2+A*v^2)
@[expose] def F (A B u v:R) := 3*u*C A B u v+K A B u v*(v*Q A B u v-S A u v*u)

lemma curve_factor (A B u v:R) : v*G B v-u*(u^2+A*v^2)=equation A B u v := by
  simp only [G,equation];ring
lemma kernel_factor (A B u v:R) :
    G B v*F A B u v-u*H A B u v=K A B u v*Q A B u v*equation A B u v := by
  rw [←curve_factor]
  simp only [F,H]
  ring

/-- The explicit regular-neighborhood coefficient removes all nilpotent
kernel directions as well: the proof only cancels declared units. -/
theorem zero_of_equation (A B u v:R) (he:equation A B u v=0) (hf:F A B u v=0)
    (hg:IsUnit (G B v)) (hh:IsUnit (H A B u v)) : u=0 ∧ v=0 := by
  have hu:u=0 := by
    apply hh.mul_right_cancel
    have h:=kernel_factor A B u v
    rw [hf,he,mul_zero,mul_zero,zero_sub,neg_eq_zero] at h
    simpa only [zero_mul] using h
  refine ⟨hu,?_⟩
  apply hg.mul_right_cancel
  have h:=curve_factor A B u v
  rw [he,hu,zero_mul,sub_zero] at h
  simpa only [zero_mul] using h

lemma origin_Q (A B:R) : Q A B 0 0=1 := by simp [Q,q]
lemma origin_S (A:R) : S A 0 0=0 := by simp [S,s]
lemma origin_C (A B:R) : C A B 0 0=1 := by simp [C,origin_Q,origin_S]
lemma origin_G (B:R) : G B 0=1 := by simp [G]
lemma origin_K (A B:R) : K A B 0 0=0 := by simp [K,origin_S]
lemma origin_H (A B:R) : H A B 0 0=3 := by simp [H,origin_G,origin_C,origin_K]

/-- Exact elimination of the actual regular slope and intercept, not a
formal-series approximation. -/
lemma slope_elimination (A B u v a b:R) (ha:a*Q A B u v=S A u v)
    (hb:b=v-a*u) : d A B a b*(Q A B u v)^3=K A B u v*(v*Q A B u v-S A u v*u) := by
  rw [←ha,hb]
  simp only [d,K]
  rw [←ha]
  ring
lemma leading_elimination (A B u v a:R) (ha:a*Q A B u v=S A u v) :
    c A B a*(Q A B u v)^3=C A B u v := by
  simp only [C,c]
  rw [←ha]
  ring
lemma F_zero_of_output (A B u v a b:R) (ha:a*Q A B u v=S A u v)
    (hb:b=v-a*u) (hout:c A B a*(-u-u-u)=d A B a b) : F A B u v=0 := by
  have hc:=leading_elimination A B u v a ha
  have hd:=slope_elimination A B u v a b ha hb
  simp only [F]
  linear_combination -3*u*hc-hd-(Q A B u v)^3*hout
end InfinityKernelNeighborhoodPolynomial318
