module
public import OriginalUniformCowanData318
public section
namespace OriginalUniformCowanLaws318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalRadixHZCertificate318 OriginalUniformCowanData318
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
@[expose] def MMVars : List PairE := [regm,regn,regBB,regCC]
@[expose] def MMTerms : List Term := [(2744,[(1,0),(2,0),(5,0),(0,3)]),(-13720,[(1,0),(1,1),(5,0),(0,3)]),(13720,[(0,1),(2,0),(5,0),(0,3)]),(-123480,[(0,1),(1,1),(5,0),(0,3)]),(296352,[(0,1),(0,2),(5,0),(0,3)]),(3125,[(0,1),(0,2),(0,5),(3,0)])]
@[expose] def MMDeg : List ℕ := [1,2,5,3]
theorem MM_ok : valid MMDeg MMTerms = true := by decide +kernel
theorem MM_cap : cap (expr MMVars MMTerms) < 2^351 := by decide +kernel
theorem MM_radix : Ev (((2:ℕ)^351:ℕ):ℤ) (expr MMVars MMTerms)=0 := by decide +kernel
theorem MM_all {K : Type*} [Field K] (z : K) (hd : ∀ v ∈ MMVars, Ev z v.2 ≠ 0) : value (ratios z MMVars) MMTerms = 0 :=
  certify z _ _ _ hd MM_ok (2^351) MM_cap MM_radix
end OriginalUniformCowanLaws318
#print axioms OriginalUniformCowanLaws318.MM_all
