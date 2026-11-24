module
public import OriginalUniformCowanData318
public section
namespace OriginalUniformCowanLaws318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalRadixHZCertificate318 OriginalUniformCowanData318
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
@[expose] def RMVars : List PairE := [regm,regn,regh,regT]
@[expose] def RMTerms : List Term := [(1,[(2,0),(0,1),(0,2),(0,1)]),(-1,[(0,2),(1,0),(0,2),(0,1)]),(-210,[(0,2),(0,1),(2,0),(1,0)]),(16134720,[(0,2),(0,1),(2,0),(0,1)])]
@[expose] def RMDeg : List ℕ := [2,1,2,1]
theorem RM_ok : valid RMDeg RMTerms = true := by decide +kernel
theorem RM_cap : cap (expr RMVars RMTerms) < 2^569 := by decide +kernel
theorem RM_radix : Ev (((2:ℕ)^569:ℕ):ℤ) (expr RMVars RMTerms)=0 := by decide +kernel
theorem RM_all {K : Type*} [Field K] (z : K) (hd : ∀ v ∈ RMVars, Ev z v.2 ≠ 0) : value (ratios z RMVars) RMTerms = 0 :=
  certify z _ _ _ hd RM_ok (2^569) RM_cap RM_radix
end OriginalUniformCowanLaws318
#print axioms OriginalUniformCowanLaws318.RM_all
