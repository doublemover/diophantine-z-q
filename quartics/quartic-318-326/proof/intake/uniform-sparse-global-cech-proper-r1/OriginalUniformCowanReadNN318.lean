module
public import OriginalUniformCowanNN318
public section
namespace OriginalUniformCowanRead318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalUniformCowanData318 OriginalUniformCowanLaws318
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {K : Type*} [Field K]
@[expose] def lawNN (n AA BB CC : K) : K := (((-1) * 75 * AA * CC) + (7 * (BB^2) * (n + (-9))))
theorem evalNN (n AA BB CC : K) : value [n,AA,BB,CC] NNTerms = lawNN n AA BB CC := by
  simp only [NNTerms,value,mno,lawNN]
  ring
theorem asNN (z : K) (hd : ∀ v ∈ NNVars, Ev z v.2 ≠ 0) : lawNN (read z regn) (read z regAA) (read z regBB) (read z regCC) = 0 := by
  have hv := NN_all z hd
  change value [(read z regn),(read z regAA),(read z regBB),(read z regCC)] NNTerms = 0 at hv
  rwa [evalNN] at hv
end OriginalUniformCowanRead318
#print axioms OriginalUniformCowanRead318.asNN
