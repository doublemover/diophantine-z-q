module
public import PELOriginalCM210NativeIntegerOrder318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace PELOriginalCM210PrimeReduction318
open PELOriginalCM210IntegralConjugation318
variable (p:ℕ) (hp:(p:ℤ)∣210)
@[expose] def reduction : R→+*ZMod p where
  toFun z := (z.re:ZMod p)
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by simp [QuadraticAlgebra.re_add]
  map_mul' x y := by
    have h210 : (210:ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd 210 p).mpr hp
    simp only [QuadraticAlgebra.re_mul,Int.cast_add,Int.cast_mul,Int.cast_neg]
    rw [h210] <;> ring
lemma reduction_surjective : Function.Surjective (reduction p hp) := by
  intro x
  obtain ⟨n,hn⟩ := ZMod.intCast_surjective x
  refine ⟨(n:R),?_⟩
  simpa [reduction] using hn
@[expose] def kernel : Ideal R := RingHom.ker (reduction p hp)
lemma mem_kernel (z:R) : z∈kernel p hp ↔ (p:ℤ)∣z.re :=
  ZMod.intCast_zmod_eq_zero_iff_dvd z.re p
lemma integer_mem : (p:R)∈kernel p hp := by
  rw [mem_kernel]; simp
lemma theta_mem : thetaR∈kernel p hp := by
  rw [mem_kernel]; simp [thetaR,QuadraticAlgebra.omega]
@[expose] def quotientEquiv : R⧸kernel p hp ≃+*ZMod p :=
  RingHom.quotientKerEquivOfSurjective (reduction_surjective p hp)
lemma quotientEquiv_mk (z:R) : quotientEquiv p hp (Ideal.Quotient.mk _ z)=(z.re:ZMod p) := rfl
end PELOriginalCM210PrimeReduction318
