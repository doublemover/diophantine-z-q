module
public import OriginalSexticJetMarked318

/-! The arithmetic certificate's remainders are unique. This is useful when
the same actual first jet is reconstructed in an independent field basis. -/
public section
noncomputable section

namespace OriginalSexticRemainderCanonical318

open Polynomial OriginalSexticJetResidues318 OriginalSexticJetMarked318

variable {E K : Type*} [Field E] [Field K] [Algebra E K]

private theorem read_any (J : Certificate E K) (i : Fin 3) (R Q : E[X])
    (hR : X^(i:ℕ)*J.G - R * J.F.derivative = J.F * Q) (v : Fin 6) :
    (R.map (algebraMap E K)).eval (J.labels v) =
      (J.labels v)^(i:ℕ)*(J.G.map (algebraMap E K)).eval (J.labels v) / branchSlope J v := by
  have h := congrArg (fun p : E[X] => (p.map (algebraMap E K)).eval (J.labels v)) hR
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    eval_sub, eval_mul, eval_pow, eval_X, ← derivative_map] at h
  rw [J.factorization, split_eval, zero_mul] at h
  exact (eq_div_iff (branchSlope_ne J v)).mpr ((sub_eq_zero.mp h).symm)

theorem unique_remainder (J : Certificate E K) (i : Fin 3) (R Q : E[X])
    (small : R.natDegree ≤ 5)
    (hR : X^(i:ℕ)*J.G - R * J.F.derivative = J.F * Q) :
    R = J.remainder i := by
  apply Polynomial.map_injective (algebraMap E K) (algebraMap E K).injective
  apply eq_of_eval_eq J.labels J.distinct
  · simpa only [natDegree_map] using small
  · simpa only [natDegree_map] using J.small i
  · intro v
    obtain ⟨Q0,e⟩ := J.relation i
    exact (read_any J i R Q hR v).trans ((read_any J i (J.remainder i) Q0 e v).symm)

/-- Adding a multiple of the defining sextic to the first coefficient
remainder does not affect the raw determinant. This guards the varying
scalar lift of a fixed arithmetic coframe, not a changed constant twist. -/
theorem same_raw_mod_F (J L : Certificate E K) (hF : L.F = J.F) (ha : L.a = J.a)
    (W : E[X]) (hG : J.G - L.G = J.F * W) : rawB J = rawB L := by
  have hR (i : Fin 3) : L.remainder i = J.remainder i := by
    obtain ⟨Q,e⟩ := L.relation i
    rw [hF] at e
    refine unique_remainder J i (L.remainder i) (Q+X^(i:ℕ)*W) (L.small i) ?_
    calc
      _ = (X^(i:ℕ)*L.G - L.remainder i * J.F.derivative) +
          X^(i:ℕ)*(J.G-L.G) := by ring
      _ = J.F * (Q+X^(i:ℕ)*W) := by rw [e,hG]; ring
  simp only [rawB, moment, hR, ha]

end OriginalSexticRemainderCanonical318

#print axioms OriginalSexticRemainderCanonical318.unique_remainder
#print axioms OriginalSexticRemainderCanonical318.same_raw_mod_F
