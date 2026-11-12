module
public import PELOriginalCM210NativeCoprimeProduct318
public import PELOriginalCM210ThetaPrincipal318
public import PELOriginalCM210FourNativePrimes318
public section
noncomputable section
namespace PELOriginalCM210ActualProductTable318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210NativePrimeResidue318 PELOriginalCM210NativeCoprimeProduct318
open PELOriginalCM210FourNativePrimes318 PELOriginalCM210ThetaPrincipal318
lemma two_three : ideal 0*ideal 1=nativeIdeal 6 (by norm_num) :=
  native_product 2 3 (by norm_num) (by norm_num) (by norm_num) (-1) 1 (by norm_num)
lemma two_five : ideal 0*ideal 2=nativeIdeal 10 (by norm_num) :=
  native_product 2 5 (by norm_num) (by norm_num) (by norm_num) (-2) 1 (by norm_num)
lemma three_five : ideal 1*ideal 2=nativeIdeal 15 (by norm_num) :=
  native_product 3 5 (by norm_num) (by norm_num) (by norm_num) 2 (-1) (by norm_num)
lemma two_three_five : (ideal 0*ideal 1)*ideal 2=nativeIdeal 30 (by norm_num) := by
  rw [two_three]
  exact native_product 6 5 (by norm_num) (by norm_num) (by norm_num) 1 (-1) (by norm_num)
lemma all_four : ((ideal 0*ideal 1)*ideal 2)*ideal 3=
    Ideal.span ({integerEquiv thetaR}:Set O) := by
  rw [two_three_five,←native_theta_principal]
  exact native_product 30 7 (by norm_num) (by norm_num) (by norm_num) 4 (-17) (by norm_num)
end PELOriginalCM210ActualProductTable318
