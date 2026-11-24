module
public import OriginalUniformCowanQ0318
public section
namespace OriginalUniformCowanRead318
open OriginalMarkedIntPolynomialCertificate318 OriginalUniformFractionCert318 OriginalUniformCowanData318 OriginalUniformCowanLaws318
set_option maxRecDepth 65536
set_option maxHeartbeats 32000000
variable {K : Type*} [Field K]
@[expose] def lawQ0 (m n p q a b T : K) : K := (((-1) * T * (a^2) * (m^2) * (n^2) * q) + ((-1) * 9 * T * (a^2) * (m^2) * n * q) + (60 * T * (a^2) * (m^2) * q) + (2 * T * (a^2) * m * (n^3) * p) + ((-1) * 22 * T * (a^2) * m * (n^2) * p) + ((-1) * T * (a^2) * m * (n^2) * q) + (60 * T * (a^2) * m * n * p) + (5 * T * (a^2) * m * n * q) + (2 * T * (a^2) * (n^3) * p) + ((-1) * 10 * T * (a^2) * (n^2) * p) + (20 * T * (a^2) * (n^2) * q) + ((-1) * 90 * T * (a^2) * n * q) + ((-1) * 2 * T * a * b * (m^3) * (n^2) * q) + ((-1) * 18 * T * a * b * (m^3) * n * q) + (120 * T * a * b * (m^3) * q) + (4 * T * a * b * (m^2) * (n^3) * p) + ((-1) * 44 * T * a * b * (m^2) * (n^2) * p) + ((-1) * 10 * T * a * b * (m^2) * (n^2) * q) + (120 * T * a * b * (m^2) * n * p) + (30 * T * a * b * (m^2) * n * q) + (2 * T * a * b * m * (n^3) * q) + (18 * T * a * b * m * (n^2) * q) + ((-1) * 120 * T * a * b * m * n * q) + ((-1) * 4 * T * a * b * (n^4) * p) + (44 * T * a * b * (n^3) * p) + (10 * T * a * b * (n^3) * q) + ((-1) * 120 * T * a * b * (n^2) * p) + ((-1) * 30 * T * a * b * (n^2) * q) + ((-1) * T * (b^2) * (m^4) * (n^2) * q) + ((-1) * 9 * T * (b^2) * (m^4) * n * q) + (60 * T * (b^2) * (m^4) * q) + (2 * T * (b^2) * (m^3) * (n^3) * p) + ((-1) * 22 * T * (b^2) * (m^3) * (n^2) * p) + ((-1) * T * (b^2) * (m^3) * (n^2) * q) + (60 * T * (b^2) * (m^3) * n * p) + (5 * T * (b^2) * (m^3) * n * q) + (2 * T * (b^2) * (m^2) * (n^3) * p) + (T * (b^2) * (m^2) * (n^3) * q) + ((-1) * 10 * T * (b^2) * (m^2) * (n^2) * p) + (29 * T * (b^2) * (m^2) * (n^2) * q) + ((-1) * 150 * T * (b^2) * (m^2) * n * q) + ((-1) * 2 * T * (b^2) * m * (n^4) * p) + (22 * T * (b^2) * m * (n^3) * p) + (T * (b^2) * m * (n^3) * q) + ((-1) * 60 * T * (b^2) * m * (n^2) * p) + ((-1) * 5 * T * (b^2) * m * (n^2) * q) + ((-1) * 2 * T * (b^2) * (n^4) * p) + (10 * T * (b^2) * (n^3) * p) + ((-1) * 20 * T * (b^2) * (n^3) * q) + (90 * T * (b^2) * (n^2) * q) + ((-1) * 3 * (m^2) * (n^3) * q) + ((-1) * 12 * (m^2) * (n^2) * q) + (315 * (m^2) * n * q) + ((-1) * 900 * (m^2) * q) + (6 * m * (n^4) * p) + ((-1) * 96 * m * (n^3) * p) + ((-1) * 3 * m * (n^3) * q) + (510 * m * (n^2) * p) + (30 * m * (n^2) * q) + ((-1) * 900 * m * n * p) + ((-1) * 75 * m * n * q) + (6 * (n^4) * p) + ((-1) * 60 * (n^3) * p) + (60 * (n^3) * q) + (150 * (n^2) * p) + ((-1) * 570 * (n^2) * q) + (1350 * n * q))
theorem evalQ0 (m n p q a b T : K) : value [m,n,p,q,a,b,T] Q0Terms = lawQ0 m n p q a b T := by
  simp only [Q0Terms,value,mno,lawQ0]
  ring
theorem asQ0 (z : K) (hd : ∀ v ∈ Q0Vars, Ev z v.2 ≠ 0) : lawQ0 (read z regm) (read z regn) (read z regp) (read z regq) (read z rega) (read z regb) (read z regT) = 0 := by
  have hv := Q0_all z hd
  change value [(read z regm),(read z regn),(read z regp),(read z regq),(read z rega),(read z regb),(read z regT)] Q0Terms = 0 at hv
  rwa [evalQ0] at hv
end OriginalUniformCowanRead318
#print axioms OriginalUniformCowanRead318.asQ0
