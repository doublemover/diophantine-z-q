module
public import ActualTwoDescentBinaryLocalComparison318
public section
noncomputable section
namespace ActualTwoDescentLocalUnitData318
open ActualTwoDescentBinaryLocalComparison318 ActualTwoDescentSignReciprocity318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

/-- An actual completed-field squareclass description. The integral unit,
its actual Jacobi symbol and the nonzero square multiplier are retained. -/
def UnitData (z : ℚ_[p]) (e b : ZMod 2) : Prop :=
  ∃ A : ℤ, IsCoprime A (p : ℤ) ∧ jacobiSym A p=sign b ∧
    ∃ r : ℚ_[p], r ≠ 0 ∧ z=((p : ℚ_[p])^e.val*A)*r^2

lemma actual_unit_data_unique (z : ℚ_[p]) (e b f c : ZMod 2)
    (H : UnitData z e b) (G : UnitData z f c) : e=f ∧ b=c := by
  obtain ⟨A,hA,sA,r,hr,hz⟩ := H
  obtain ⟨D,hD,sD,s,hs,hw⟩ := G
  obtain ⟨he,hb⟩ := actual_binary_coordinate_comparison z e f A D hA hD r s hr hs hz hw
  exact ⟨he,sign_injective (sA.symm.trans (hb.trans sD))⟩

lemma actual_unit_data_square_scale (z r : ℚ_[p]) (hr : r ≠ 0)
    (e b : ZMod 2) (H : UnitData z e b) : UnitData (z*r^2) e b := by
  obtain ⟨A,hA,hs,s,hs0,he⟩ := H
  refine ⟨A,hA,hs,s*r,mul_ne_zero hs0 hr,?_⟩
  rw [he,mul_pow]
  ring

/-- Multiplication adds the two binary invariants. When both valuations
are odd the extra prime square is explicitly absorbed into the multiplier. -/
theorem actual_unit_data_mul (z w : ℚ_[p]) (e b f c : ZMod 2)
    (H : UnitData z e b) (G : UnitData w f c) : UnitData (z*w) (e+f) (b+c) := by
  obtain ⟨A,hA,sA,r,hr,hz⟩ := H
  obtain ⟨D,hD,sD,s,hs,hw⟩ := G
  refine ⟨A*D,hA.mul_left hD,?_,(p : ℚ_[p])^((e.val+f.val)/2)*r*s,?_,?_⟩
  · rw [jacobiSym.mul_left,sA,sD,sign_add]
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) hr) hs
  · rw [hz,hw]
    fin_cases e <;> fin_cases f <;> norm_num <;> push_cast <;> ring

lemma actual_unit_data_one : UnitData (1 : ℚ_[p]) 0 0 := by
  refine ⟨1,isCoprime_one_left,?_,1,one_ne_zero,?_⟩
  · rw [jacobiSym.one_left,sign_zero]
  · norm_num

end ActualTwoDescentLocalUnitData318
