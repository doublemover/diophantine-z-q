module
public import ActualTwoDescentLargeLocalIdentity318
public section
noncomputable section
namespace ActualTwoDescentLocalIdentityAvoidance318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentLiteralKummerClasses318 ActualTwoDescentLargeLocalIdentity318
open ActualTwoDescentSquareClassQuotient318
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

def localPointSize (n : ℕ) : Point (n : ℚ_[p]) → ℝ
  | .zero => 0
  | .some x _ _ => ‖x‖

lemma local_point_size_nonneg (n : ℕ) (P : Point (n : ℚ_[p])) : 0 ≤ localPointSize n P := by
  cases P with
  | zero => exact le_refl _
  | some x y h => exact norm_nonneg _

/-- The actual identity Kummer class contains a point outside ANY finite set. -/
theorem actual_identity_class_avoids_finite (n : ℕ) (hn : n ≠ 0)
    (S : Finset (Point (n : ℚ_[p]))) :
    ∃ Q : Point (n : ℚ_[p]), Q ∉ S ∧ kummerClass (n : ℚ_[p]) (Nat.cast_ne_zero.mpr hn) Q=1 := by
  let M : ℝ := ∑ P ∈ S, localPointSize n P
  have hM : 0 ≤ M := Finset.sum_nonneg (fun P _ => local_point_size_nonneg n P)
  obtain ⟨P,H,hlarge⟩ := actual_large_identity_local_point (p:=p) n M hM
  let h := curve_nonsingular (n : ℚ_[p]) P.x P.y (Nat.cast_ne_zero.mpr hn) P.curve
  let Q : Point (n : ℚ_[p]) := .some P.x P.y h
  have hQ : kummerClass (n : ℚ_[p]) (Nat.cast_ne_zero.mpr hn) Q=1 := by
    have he := (actual_kummer_pair_iff (n : ℚ_[p]) P.x P.y 1 1
      (Nat.cast_ne_zero.mpr hn) h P.plus_ne P.minus_ne one_ne_zero one_ne_zero).mpr H
    simpa only [class_of_one] using he
  refine ⟨Q,?_,hQ⟩
  intro hmem
  have hle : localPointSize n Q ≤ M :=
    Finset.single_le_sum (fun R _ => local_point_size_nonneg n R) hmem
  exact (not_le_of_gt hlarge) hle

end ActualTwoDescentLocalIdentityAvoidance318
