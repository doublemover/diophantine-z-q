module
public import PELOriginalCM210FourPrimeSquares318
public import Mathlib.RingTheory.ClassGroup.Basic
public section
noncomputable section
namespace PELOriginalCM210NativePrimeClasses318
open PELOriginalCM210NativeIntegerOrder318 PELOriginalCM210FourNativePrimes318
open PELOriginalCM210FourPrimeSquares318
open scoped nonZeroDivisors
@[expose] def nonzeroIdeal (i:Fin 4) : (Ideal O)⁰ :=
  ⟨ideal i,mem_nonZeroDivisors_of_ne_zero (show ideal i≠0 from nonzero i)⟩
@[expose] def primeClass (i:Fin 4) : ClassGroup O := ClassGroup.mk0 (nonzeroIdeal i)
lemma class_square (i:Fin 4) : (primeClass i)^2=1 := by
  rw [primeClass,←map_pow]
  apply (ClassGroup.mk0_eq_one_iff ((nonzeroIdeal i)^2).property).mpr
  change ((ideal i)^2).IsPrincipal
  rw [native_square]
  infer_instance
lemma class_inverse (i:Fin 4) : (primeClass i)⁻¹=primeClass i := by
  have h := class_square i
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h
end PELOriginalCM210NativePrimeClasses318
