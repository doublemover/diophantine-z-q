module
public import OriginalUniformCowanQ1318
public section
namespace OriginalUniformCowanRead318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalUniformCowanData318 OriginalUniformCowanLaws318
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {K : Type*} [Field K]
@[expose] def lawQ1 (m n p q a b T : K) : K := (((-1) * T * (a^2) * m * (n^2) * q) + ((-1) * 9 * T * (a^2) * m * n * q) + (60 * T * (a^2) * m * q) + (2 * T * (a^2) * (n^3) * p) + ((-1) * 22 * T * (a^2) * (n^2) * p) + ((-1) * 5 * T * (a^2) * (n^2) * q) + (60 * T * (a^2) * n * p) + (15 * T * (a^2) * n * q) + ((-1) * 2 * T * a * b * (m^2) * (n^2) * q) + ((-1) * 18 * T * a * b * (m^2) * n * q) + (120 * T * a * b * (m^2) * q) + (4 * T * a * b * m * (n^3) * p) + ((-1) * 44 * T * a * b * m * (n^2) * p) + ((-1) * 2 * T * a * b * m * (n^2) * q) + (120 * T * a * b * m * n * p) + (10 * T * a * b * m * n * q) + (4 * T * a * b * (n^3) * p) + ((-1) * 20 * T * a * b * (n^2) * p) + (40 * T * a * b * (n^2) * q) + ((-1) * 180 * T * a * b * n * q) + ((-1) * T * (b^2) * (m^3) * (n^2) * q) + ((-1) * 9 * T * (b^2) * (m^3) * n * q) + (60 * T * (b^2) * (m^3) * q) + (2 * T * (b^2) * (m^2) * (n^3) * p) + ((-1) * 22 * T * (b^2) * (m^2) * (n^2) * p) + ((-1) * 5 * T * (b^2) * (m^2) * (n^2) * q) + (60 * T * (b^2) * (m^2) * n * p) + (15 * T * (b^2) * (m^2) * n * q) + (T * (b^2) * m * (n^3) * q) + (9 * T * (b^2) * m * (n^2) * q) + ((-1) * 60 * T * (b^2) * m * n * q) + ((-1) * 2 * T * (b^2) * (n^4) * p) + (22 * T * (b^2) * (n^3) * p) + (5 * T * (b^2) * (n^3) * q) + ((-1) * 60 * T * (b^2) * (n^2) * p) + ((-1) * 15 * T * (b^2) * (n^2) * q) + (3 * m * (n^3) * q) + (12 * m * (n^2) * q) + ((-1) * 315 * m * n * q) + (900 * m * q) + ((-1) * 6 * (n^4) * p) + (96 * (n^3) * p) + (15 * (n^3) * q) + ((-1) * 510 * (n^2) * p) + ((-1) * 120 * (n^2) * q) + (900 * n * p) + (225 * n * q))
theorem evalQ1 (m n p q a b T : K) : value [m,n,p,q,a,b,T] Q1Terms = lawQ1 m n p q a b T := by
  simp only [Q1Terms,value,mno,lawQ1]
  ring
theorem asQ1 (z : K) (hd : ∀ v ∈ Q1Vars, Ev z v.2 ≠ 0) : lawQ1 (read z regm) (read z regn) (read z regp) (read z regq) (read z rega) (read z regb) (read z regT) = 0 := by
  have hv := Q1_all z hd
  change value [(read z regm),(read z regn),(read z regp),(read z regq),(read z rega),(read z regb),(read z regT)] Q1Terms = 0 at hv
  rwa [evalQ1] at hv
end OriginalUniformCowanRead318
#print axioms OriginalUniformCowanRead318.asQ1
