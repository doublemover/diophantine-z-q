module
public import PELOriginalCM210PrimeReduction318
public section
noncomputable section
namespace PELOriginalCM210PrimeSpan318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210PrimeReduction318
variable (p:ℕ) (hp:(p:ℤ)∣210)
lemma kernel_eq_span : kernel p hp=Ideal.span ({(p:R),thetaR}:Set R) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a,ha⟩ := (mem_kernel p hp z).mp hz
    have he : z=(a:R)*(p:R)+(z.im:R)*thetaR := by
      ext
      · simpa [QuadraticAlgebra.re_mul,thetaR,QuadraticAlgebra.omega,mul_comm] using ha
      · simp [QuadraticAlgebra.im_mul,thetaR,QuadraticAlgebra.omega]
    rw [he]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
    rcases hz with rfl|rfl
    · exact integer_mem p hp
    · exact theta_mem p hp
/-- Explicit universal two-generator expression, not just an index count. -/
lemma kernel_expression (z:R) (hz:z∈kernel p hp) :
    ∃a:ℤ,z=(a:R)*(p:R)+(z.im:R)*thetaR := by
  obtain ⟨a,ha⟩ := (mem_kernel p hp z).mp hz
  refine ⟨a,?_⟩
  ext
  · simpa [QuadraticAlgebra.re_mul,thetaR,QuadraticAlgebra.omega,mul_comm] using ha
  · simp [QuadraticAlgebra.im_mul,thetaR,QuadraticAlgebra.omega]
end PELOriginalCM210PrimeSpan318
