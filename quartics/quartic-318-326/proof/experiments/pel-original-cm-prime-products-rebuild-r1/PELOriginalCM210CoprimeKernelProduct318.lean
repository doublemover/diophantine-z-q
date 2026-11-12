module
public import PELOriginalCM210PrimeSpan318
public import Mathlib.RingTheory.Ideal.Operations
public section
noncomputable section
namespace PELOriginalCM210CoprimeKernelProduct318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210PrimeReduction318
open PELOriginalCM210PrimeSpan318
variable (m n:ℕ) (hm:(m:ℤ)∣210) (hn:(n:ℤ)∣210) (hmn:((m*n:ℕ):ℤ)∣210)
lemma product_le : kernel m hm*kernel n hn≤kernel (m*n) hmn := by
  apply Ideal.mul_le.mpr
  intro z hz w hw
  obtain ⟨a,ha⟩ := (mem_kernel m hm z).mp hz
  obtain ⟨c,hc⟩ := (mem_kernel n hn w).mp hw
  obtain ⟨q,hq⟩ := hmn
  apply (mem_kernel (m*n) hmn (z*w)).mpr
  refine ⟨a*c-q*z.im*w.im,?_⟩
  have hneg : (-210:ℤ)= -((m:ℤ)*(n:ℤ)*q) := by
    push_cast at hq
    linarith
  simp only [QuadraticAlgebra.re_mul,ha,hc,Nat.cast_mul,hneg]
  ring
lemma product_eq (a c:ℤ) (h:a*(m:ℤ)+c*(n:ℤ)=1) :
    kernel m hm*kernel n hn=kernel (m*n) hmn := by
  apply le_antisymm (product_le m n hm hn hmn)
  rw [kernel_eq_span]
  apply Ideal.span_le.mpr
  intro z hz
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
  rcases hz with rfl|rfl
  · simpa only [Nat.cast_mul] using Ideal.mul_mem_mul (integer_mem m hm) (integer_mem n hn)
  · have h1 := Ideal.mul_mem_mul (integer_mem m hm) (theta_mem n hn)
    have h2 := Ideal.mul_mem_mul (theta_mem m hm) (integer_mem n hn)
    have hs := Ideal.add_mem (kernel m hm*kernel n hn)
      (Ideal.mul_mem_left _ (a:R) h1) (Ideal.mul_mem_left _ (c:R) h2)
    have he : (a:R)*((m:R)*thetaR)+(c:R)*(thetaR*(n:R))=thetaR := by
      ext
      · simp [thetaR,QuadraticAlgebra.omega,QuadraticAlgebra.re_mul]
      · simpa [thetaR,QuadraticAlgebra.omega,QuadraticAlgebra.im_mul] using h
    rwa [he] at hs
end PELOriginalCM210CoprimeKernelProduct318
