module
public import ActualTwoDescentFourTwoAdicClasses318
public section
noncomputable section
namespace ActualTwoDescentArchimedeanRepresentation318
open ActualTwoDescentExceptionalLocalPoints318
set_option maxHeartbeats 16000000

/-- Actual real representation of both original Kummer coordinates, with
all cubic factors and square multipliers nonzero. -/
def RealRepresented (n M L : ℕ) : Prop :=
  ∃ x y u v : ℝ, x ≠ 0 ∧ x-n ≠ 0 ∧ x+3*n ≠ 0 ∧ u ≠ 0 ∧ v ≠ 0 ∧
    y^2=x*(x-n)*(x+3*n) ∧ x+3*n=(M : ℝ)*u^2 ∧ x-n=(L : ℝ)*v^2

theorem actual_positive_real_representation (M n : ℕ) (hM : 0<M) : RealRepresented n M 1 := by
  obtain ⟨x,y,u,v,hx,hu,hv,hc,hA,hB⟩ := actual_real_kummer_point M n hM
  refine ⟨x,y,u,v,hx,?_,?_,hu,hv,hc,hA,?_⟩
  · rw [hB]
    exact pow_ne_zero _ hv
  · rw [hA]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hM.ne') (pow_ne_zero _ hu)
  · simpa only [Nat.cast_one,one_mul] using hB

end ActualTwoDescentArchimedeanRepresentation318
