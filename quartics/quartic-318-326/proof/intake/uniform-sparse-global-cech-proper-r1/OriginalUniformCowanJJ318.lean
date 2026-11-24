module
public import OriginalUniformCowanData318
public section
namespace OriginalUniformCowanLaws318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalRadixHZCertificate318 OriginalUniformCowanData318
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
@[expose] def JJVars : List PairE := [regAA,regBB,regCC,regJ]
@[expose] def JJTerms : List Term := [(20,[(1,0),(0,2),(1,0),(0,1)]),(14,[(0,1),(2,0),(0,1),(0,1)]),(1,[(0,1),(0,2),(1,0),(1,0)])]
@[expose] def JJDeg : List ℕ := [1,2,1,1]
theorem JJ_ok : valid JJDeg JJTerms = true := by decide +kernel
theorem JJ_cap : cap (expr JJVars JJTerms) < 2^89 := by decide +kernel
theorem JJ_radix : Ev (((2:ℕ)^89:ℕ):ℤ) (expr JJVars JJTerms)=0 := by decide +kernel
theorem JJ_all {K : Type*} [Field K] (z : K) (hd : ∀ v ∈ JJVars, Ev z v.2 ≠ 0) : value (ratios z JJVars) JJTerms = 0 :=
  certify z _ _ _ hd JJ_ok (2^89) JJ_cap JJ_radix
end OriginalUniformCowanLaws318
#print axioms OriginalUniformCowanLaws318.JJ_all
