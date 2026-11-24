module
public import OriginalUniformCowanData318
public section
namespace OriginalUniformCowanLaws318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalRadixHZCertificate318 OriginalUniformCowanData318
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
@[expose] def NNVars : List PairE := [regn,regAA,regBB,regCC]
@[expose] def NNTerms : List Term := [(7,[(1,0),(0,1),(2,0),(0,1)]),(-75,[(0,1),(1,0),(0,2),(1,0)]),(-63,[(0,1),(0,1),(2,0),(0,1)])]
@[expose] def NNDeg : List ℕ := [1,1,2,1]
theorem NN_ok : valid NNDeg NNTerms = true := by decide +kernel
theorem NN_cap : cap (expr NNVars NNTerms) < 2^100 := by decide +kernel
theorem NN_radix : Ev (((2:ℕ)^100:ℕ):ℤ) (expr NNVars NNTerms)=0 := by decide +kernel
theorem NN_all {K : Type*} [Field K] (z : K) (hd : ∀ v ∈ NNVars, Ev z v.2 ≠ 0) : value (ratios z NNVars) NNTerms = 0 :=
  certify z _ _ _ hd NN_ok (2^100) NN_cap NN_radix
end OriginalUniformCowanLaws318
#print axioms OriginalUniformCowanLaws318.NN_all
