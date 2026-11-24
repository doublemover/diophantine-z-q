module
public import OriginalUniformCowanJJ318
public section
namespace OriginalUniformCowanRead318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalUniformCowanData318 OriginalUniformCowanLaws318
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {K : Type*} [Field K]
@[expose] def lawJJ (AA BB CC J : K) : K := ((14 * (BB^2)) + (CC * ((20 * AA) + J)))
theorem evalJJ (AA BB CC J : K) : value [AA,BB,CC,J] JJTerms = lawJJ AA BB CC J := by
  simp only [JJTerms,value,mno,lawJJ]
  ring
theorem asJJ (z : K) (hd : ∀ v ∈ JJVars, Ev z v.2 ≠ 0) : lawJJ (read z regAA) (read z regBB) (read z regCC) (read z regJ) = 0 := by
  have hv := JJ_all z hd
  change value [(read z regAA),(read z regBB),(read z regCC),(read z regJ)] JJTerms = 0 at hv
  rwa [evalJJ] at hv
end OriginalUniformCowanRead318
#print axioms OriginalUniformCowanRead318.asJJ
