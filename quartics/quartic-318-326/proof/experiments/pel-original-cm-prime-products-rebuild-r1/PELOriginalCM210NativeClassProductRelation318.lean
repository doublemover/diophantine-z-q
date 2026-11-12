module
public import PELOriginalCM210ActualProductTable318
public import PELOriginalCM210NativePrimeClasses318
public section
noncomputable section
namespace PELOriginalCM210NativeClassProductRelation318
open PELOriginalCM210FourNativePrimes318 PELOriginalCM210NativePrimeClasses318
open PELOriginalCM210ActualProductTable318
lemma class_product : ((primeClass 0*primeClass 1)*primeClass 2)*primeClass 3=1 := by
  simp only [primeClass,←map_mul]
  apply (ClassGroup.mk0_eq_one_iff
    (((nonzeroIdeal 0*nonzeroIdeal 1)*nonzeroIdeal 2)*nonzeroIdeal 3).property).mpr
  change (((ideal 0*ideal 1)*ideal 2)*ideal 3).IsPrincipal
  rw [all_four]
  infer_instance
lemma fourth_class : primeClass 3=(primeClass 0*primeClass 1)*primeClass 2 := by
  have h : ((primeClass 0*primeClass 1)*primeClass 2)⁻¹=primeClass 3 :=
    inv_eq_of_mul_eq_one_right class_product
  simpa only [mul_inv_rev,class_inverse,mul_comm,mul_left_comm,mul_assoc] using h.symm
end PELOriginalCM210NativeClassProductRelation318
