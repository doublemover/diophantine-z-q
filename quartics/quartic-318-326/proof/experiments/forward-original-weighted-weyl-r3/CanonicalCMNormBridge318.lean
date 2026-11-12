module
public import GaussianNormUniqueness318
public import CanonicalSelectedCounts318
public section
noncomputable section
namespace CanonicalCMNormBridge318
open FiniteCurveCharacterCount318 CanonicalSelectedCounts318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

/-- A constructed integral CM/Jacobi-sum norm and the actual canonical trace
suffice; Gaussian unit/associate classification is proved here, not an input. -/
theorem canonical_of_norm (a b c d : ℤ)
    (hray : GaussianRayQuadratic318.Ray p a b)
    (hnorm : c^2+d^2=(p:ℤ)) (hcod : c%2=1)
    (htrace : traceSum (1:ZMod p)=2*c) : CanonicalCM p a := by
  have hb : b%2=0 := by have h := hray.2.2; omega
  have he := GaussianNormUniqueness318.odd_real_square p (Fact.out : p.Prime)
    a b c d hray.1.symm hnorm hb hcod
  change (traceSum (1:ZMod p))^2=4*a^2
  rw [htrace]
  nlinarith

/-- The sign convention for Frobenius versus the character sum is harmless:
both actual conventions feed the same proved trace-square comparison. -/
theorem canonical_of_signed_norm (a b c d : ℤ)
    (hray : GaussianRayQuadratic318.Ray p a b)
    (hnorm : c^2+d^2=(p:ℤ)) (hcod : c%2=1)
    (htrace : traceSum (1:ZMod p)=2*c ∨ traceSum (1:ZMod p)= -(2*c)) :
    CanonicalCM p a := by
  rcases htrace with h|h
  · exact canonical_of_norm p a b c d hray hnorm hcod h
  · have hn : (-c)^2+d^2=(p:ℤ) := by simpa only [neg_sq] using hnorm
    have ho : (-c)%2=1 := by omega
    exact canonical_of_norm p a b (-c) d hray hn ho (by linarith)

end CanonicalCMNormBridge318
