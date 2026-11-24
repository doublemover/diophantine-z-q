module
public import OriginalUniformCowanRM318
public section
namespace OriginalUniformCowanRead318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalUniformCowanData318 OriginalUniformCowanLaws318
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {K : Type*} [Field K]
@[expose] def lawRM (m n h T : K) : K := (((-1) * (h^2) * ((210 * T) + (-16134720))) + (m^2) + ((-1) * n))
theorem evalRM (m n h T : K) : value [m,n,h,T] RMTerms = lawRM m n h T := by
  simp only [RMTerms,value,mno,lawRM]
  ring
theorem asRM (z : K) (hd : ∀ v ∈ RMVars, Ev z v.2 ≠ 0) : lawRM (read z regm) (read z regn) (read z regh) (read z regT) = 0 := by
  have hv := RM_all z hd
  change value [(read z regm),(read z regn),(read z regh),(read z regT)] RMTerms = 0 at hv
  rwa [evalRM] at hv
end OriginalUniformCowanRead318
#print axioms OriginalUniformCowanRead318.asRM
