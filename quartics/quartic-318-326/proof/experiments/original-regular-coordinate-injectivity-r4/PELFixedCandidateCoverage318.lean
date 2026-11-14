module
public import PELFixedCandidateConjugators318
public import PELOriginalFixedPolygonSearch318
public section
noncomputable section
namespace PELFixedCandidateCoverage318
open PELPrincipalOrderCoordinates318 PELIntegralEllipticObstructions318
open PELOriginalFixedIntegralCoordinates318 PELFixedNormalizerFiniteSearch318
open PELFixedCandidateConjugators318
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096

@[expose] def signedCoordinate (n : ℕ) (positive : Bool) : ℤ :=
  if positive then (n:ℤ) else -(n:ℤ)
@[expose] def signedCandidate (t : ℕ × ℕ × ℕ) (sa sd : Bool) : Coordinates :=
  let a := signedCoordinate t.2.1 sa
  let d := signedCoordinate t.2.2 sd
  ![a,((t.1:ℤ)-d)/2,-2*a,d]

/-- Restore EVERY independent sign, retaining the original order parity.
Zero-coordinate sign repetitions merely choose the same listed candidate. -/
theorem signed_rows_covered (i : Fin 5) (t : ℕ × ℕ × ℕ) (ht : t∈rows i)
    (sa sd : Bool) : ∃ k : Fin 77,label k=i ∧ candidate k=signedCandidate t sa sd := by
  fin_cases i
  · simp [rows] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals cases sa <;> cases sd <;> decide
  · simp [rows] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals cases sa <;> cases sd <;> decide
  · simp [rows] at ht
    rcases ht with rfl | rfl
    all_goals cases sa <;> cases sd <;> decide
  · simp [rows] at ht
    rcases ht with rfl | rfl
    all_goals cases sa <;> cases sd <;> decide
  · simp [rows] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals cases sa <;> cases sd <;> decide

theorem sign_choice (z : ℤ) : ∃ b : Bool,signedCoordinate z.natAbs b=z := by
  rcases le_total 0 z with hp | hn
  · exact ⟨true,by simp [signedCoordinate,Int.natCast_natAbs,abs_of_nonneg hp]⟩
  · exact ⟨false,by simp [signedCoordinate,Int.natCast_natAbs,abs_of_nonpos hn]⟩

/-- The finite signed list recovers the ENTIRE original integer coordinate
vector, not just its two Klein ratios or a projective multiple. -/
theorem original_candidate_covered (i : Fin 5) (x : Coordinates) (ht : trace x=0)
    (hr : 0<rotationCoordinate x)
    (hrows : ((rotationCoordinate x).toNat,(x 0).natAbs,(x 3).natAbs)∈rows i) :
    ∃ k : Fin 77,label k=i ∧ candidate k=x := by
  obtain ⟨sa,ha⟩ := sign_choice (x 0)
  obtain ⟨sd,hd⟩ := sign_choice (x 3)
  obtain ⟨k,hki,hk⟩ := signed_rows_covered i _ hrows sa sd
  refine ⟨k,hki,hk.trans ?_⟩
  have hrot : ((rotationCoordinate x).toNat:ℤ)=rotationCoordinate x :=
    Int.toNat_of_nonneg hr.le
  have h2 : x 2= -2*x 0 := by unfold trace at ht; omega
  ext j
  fin_cases j
  · simpa only [signedCandidate,Matrix.cons_val_zero] using ha
  · simp only [signedCandidate,Matrix.cons_val_one,ha,hd,hrot]
    unfold rotationCoordinate
    omega
  · simp only [signedCandidate,Matrix.cons_val_two,ha,h2]
  · simpa only [signedCandidate,Matrix.cons_val_three] using hd
end PELFixedCandidateCoverage318
