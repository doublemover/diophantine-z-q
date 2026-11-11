module
public import ActualAffineQuarticEliminant318
public section
noncomputable section
namespace ActualQuarticRegularNonzero318
open TernaryQuadraticLineCover318 OriginalAffineSieveEliminants318 ActualAffineQuarticEliminant318
set_option maxHeartbeats 9000000

/-- The genuine second quadratic is HOMOGENEOUS. At offset zero its
only affine root is zero, whereas K has constant t²(t+2)². This exact
value constructs nonvanishing of the offset eliminant in the regular
integer-label case, without a generic-position or resultant hypothesis. -/
theorem at_zero (κ t : ℤ) (d : Vector ℤ) :
    actualEliminant κ t 0 d=(fA true κ t d)^7*t^4*(t+2)^4 := by
  simp [actualEliminant,ActualQuadraticQuarticEliminant318.eliminant,
    ActualQuadraticQuarticEliminant318.linearTerm,ActualQuadraticQuarticEliminant318.constantTerm,
    fA,fB,fC,LiteralAdjacentNormSlice318.P',k4,k3,k2,k1,k0,r2,r1,r0]
  ring

theorem regular_nonzero (κ t : ℤ) (d : Vector ℤ)
    (ht : t≠0) (ht2 : t+2≠0) (hA : fA true κ t d≠0) :
    actualEliminant κ t 0 d≠0 := by
  rw [at_zero]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 7 hA) (pow_ne_zero 4 ht)) (pow_ne_zero 4 ht2)

end ActualQuarticRegularNonzero318
