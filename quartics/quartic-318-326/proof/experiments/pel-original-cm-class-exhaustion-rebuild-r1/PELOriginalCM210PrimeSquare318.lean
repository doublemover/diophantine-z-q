module
public import PELOriginalCM210PrimeSpan318
public import Mathlib.RingTheory.Ideal.Operations
public section
noncomputable section
namespace PELOriginalCM210PrimeSquare318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210PrimeReduction318
variable (p:ℕ) (hp:(p:ℤ)∣210)
lemma square_le_principal : kernel p hp*kernel p hp≤Ideal.span ({(p:R)}:Set R) := by
  apply Ideal.mul_le.mpr
  intro z hz w hw
  obtain ⟨a,ha⟩ := (mem_kernel p hp z).mp hz
  obtain ⟨c,hc⟩ := (mem_kernel p hp w).mp hw
  obtain ⟨q,hq⟩ := hp
  apply Ideal.mem_span_singleton.mpr
  refine ⟨⟨(p:ℤ)*a*c-q*z.im*w.im,a*w.im+z.im*c⟩,?_⟩
  have hneg : (-210:ℤ)= -((p:ℤ)*q) := by linarith
  ext <;> simp [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,ha,hc,hneg] <;> ring
lemma square_eq_principal (a c:ℤ) (h:a*(p:ℤ)^2-c*210=p) :
    kernel p hp*kernel p hp=Ideal.span ({(p:R)}:Set R) := by
  apply le_antisymm (square_le_principal p hp)
  apply Ideal.span_le.mpr
  intro z hz
  have hz' : z=(p:R) := Set.mem_singleton_iff.mp hz
  subst z
  have hpp := Ideal.mul_mem_mul (integer_mem p hp) (integer_mem p hp)
  have htt := Ideal.mul_mem_mul (theta_mem p hp) (theta_mem p hp)
  have hm := Ideal.add_mem (kernel p hp*kernel p hp)
    (Ideal.mul_mem_left _ (a:R) hpp) (Ideal.mul_mem_left _ (c:R) htt)
  have he : (a:R)*((p:R)*(p:R))+(c:R)*(thetaR*thetaR)=(p:R) := by
    ext
    · simpa [QuadraticAlgebra.re_mul,thetaR,QuadraticAlgebra.omega,pow_two,sub_eq_add_neg] using h
    · simp [QuadraticAlgebra.im_mul,thetaR,QuadraticAlgebra.omega]
  rwa [he] at hm
end PELOriginalCM210PrimeSquare318
