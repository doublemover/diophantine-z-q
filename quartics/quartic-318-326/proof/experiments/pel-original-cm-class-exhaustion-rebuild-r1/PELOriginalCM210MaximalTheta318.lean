module
public import PELOriginalCM210NativeClassProductRelation318
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public section
noncomputable section
namespace PELOriginalCM210MaximalTheta318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210PrimeReduction318 PELOriginalCM210PrimeSpan318
open PELOriginalCM210NativePrimeResidue318 PELOriginalCM210FourNativePrimes318
@[expose] def theta : O := integerEquiv thetaR
lemma theta_square : theta^2=(-210:O) := by
  have h : thetaR^2=(-210:R) := by
    ext <;> norm_num [thetaR,QuadraticAlgebra.omega,
      pow_two,QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul]
  simpa [theta] using congrArg integerEquiv h
lemma ideal_le (P:Ideal O) (i:Fin 4) (hp:(PELPrimeNormalizerData318.prime i:O)∈P)
    (ht:theta∈P) : ideal i≤P := by
  intro z hz
  obtain ⟨x,rfl⟩ := integerEquiv.surjective z
  have hx := (image_mem _ _ x).mp hz
  obtain ⟨a,ha⟩ := kernel_expression _ _ x hx
  rw [ha]
  simp only [map_add,map_mul,map_intCast,map_natCast]
  exact P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ ht)
lemma prime_over_ramified (P:Ideal O) [P.IsMaximal] (i:Fin 4)
    (hp:(PELPrimeNormalizerData318.prime i:O)∈P) : P=ideal i := by
  obtain ⟨q,hq⟩ := prime_divides i
  have h210 : (210:O)=(PELPrimeNormalizerData318.prime i:O)*(q:O) := by
    exact_mod_cast hq
  have hs : theta^2∈P := by
    rw [theta_square]
    apply P.neg_mem
    rw [h210]
    exact P.mul_mem_right _ hp
  have ht : theta∈P := (Ideal.IsPrime.pow_mem_iff_mem inferInstance _ (by decide:0<2)).mp hs
  exact ((isPrime i).isMaximal (nonzero i)).eq_of_le
    (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) (ideal_le P i hp ht) |>.symm
end PELOriginalCM210MaximalTheta318
