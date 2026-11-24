module
public import OriginalUniformCowanData318
public section
namespace OriginalUniformCowanDerivative318
open OriginalMarkedIntPolynomialCertificate318 OriginalRadixHZCertificate318 OriginalUniformFractionCert318 OriginalUniformCowanData318 OriginalPhysicalNaganoFirstJet318
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
@[expose] def dNum (u v : List ℤ) : E :=
 .add (.mul (.p (dcoeff u)) (.p v)) (.scale (-1) (.mul (.p u) (.p (dcoeff v))))
@[expose] def compat (u v du dv : List ℤ) : E :=
 .add (.mul (.p du) (.mul (.p v) (.p v))) (.scale (-1) (.mul (.p dv) (dNum u v)))
@[expose] noncomputable def quotientJet {K : Type*} [Field K] (z : K) (u v : List ℤ) : K :=
 (dH z u * horner z v - horner z u * dH z v) / (horner z v)^2

theorem read_derivative {K : Type*} [Field K] (z : K) (u v du dv : List ℤ)
    (h₁ : horner z v ≠ 0) (h₂ : horner z dv ≠ 0) (h : Ev z (compat u v du dv)=0) :
    read z (.p du,.p dv)=quotientJet z u v := by
  simp only [compat,dNum,Ev,Int.cast_neg,Int.cast_one,neg_one_mul] at h
  unfold OriginalUniformCowanData318.read quotientJet
  simp only [Ev,eval_derivative,OriginalPhysicalNaganoReadback318.h]
  field_simp
  linear_combination h

theorem m_jet {K : Type*} [Field K] (z : K) (h₁ : horner z regmDen≠0) (h₂ : horner z regpDen≠0) :
    read z regp=quotientJet z regmNum regmDen := by
  apply read_derivative _ _ _ _ _ h₁ h₂
  exact certificate z (2^2048) _ (by decide +kernel) (by decide +kernel)
theorem n_jet {K : Type*} [Field K] (z : K) (h₁ : horner z regnDen≠0) (h₂ : horner z regqDen≠0) :
    read z regq=quotientJet z regnNum regnDen := by
  apply read_derivative _ _ _ _ _ h₁ h₂
  exact certificate z (2^2048) _ (by decide +kernel) (by decide +kernel)
end OriginalUniformCowanDerivative318
#print axioms OriginalUniformCowanDerivative318.m_jet
#print axioms OriginalUniformCowanDerivative318.n_jet
