module
public import OriginalUniformCowanMM318
public section
namespace OriginalUniformCowanRead318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalUniformCowanData318 OriginalUniformCowanLaws318
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {K : Type*} [Field K]
@[expose] def lawMM (m n BB CC : K) : K := ((2744 * (BB^5) * ((m * n * (n + (-5))) + (5 * (n^2)) + ((-1) * 45 * n) + 108)) + (3125 * (CC^3)))
theorem evalMM (m n BB CC : K) : value [m,n,BB,CC] MMTerms = lawMM m n BB CC := by
  simp only [MMTerms,value,mno,lawMM]
  ring
theorem asMM (z : K) (hd : ∀ v ∈ MMVars, Ev z v.2 ≠ 0) : lawMM (read z regm) (read z regn) (read z regBB) (read z regCC) = 0 := by
  have hv := MM_all z hd
  change value [(read z regm),(read z regn),(read z regBB),(read z regCC)] MMTerms = 0 at hv
  rwa [evalMM] at hv
end OriginalUniformCowanRead318
#print axioms OriginalUniformCowanRead318.asMM
