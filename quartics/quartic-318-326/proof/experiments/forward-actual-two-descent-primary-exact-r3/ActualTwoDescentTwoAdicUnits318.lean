module
public import ActualTwoDescentThreeAdicSecondSquare318
public section
noncomputable section
namespace ActualTwoDescentTwoAdicUnits318
open ActualTwoDescentLocalValuationTools318
set_option maxHeartbeats 16000000

lemma actual_two_unit_lift (x : ℚ_[2]) (hx : x ≠ 0) (hv : x.valuation=0) :
    ∃ X : ℤ_[2], (X : ℚ_[2])=x ∧ IsUnit X := by
  have hn := actual_norm_one_of_valuation_zero x hx hv
  let X : ℤ_[2] := ⟨x,hn.le⟩
  refine ⟨X,rfl,PadicInt.isUnit_iff.mpr ?_⟩
  exact hn

lemma actual_unit_residue_two (X : ℤ_[2]) (hX : IsUnit X) : PadicInt.toZMod X=1 := by
  have hz : PadicInt.toZMod X ≠ 0 := (hX.map PadicInt.toZMod).ne_zero
  have h : ∀ z : ZMod 2, z ≠ 0 → z=1 := by decide
  exact h _ hz

/-- Two actual2-adic units have difference of positive valuation, proved
using the actual residue map, not an assumption about unit parity. -/
theorem actual_two_unit_difference_positive (x y : ℚ_[2])
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x-y ≠ 0)
    (vx : x.valuation=0) (vy : y.valuation=0) : 0 < (x-y).valuation := by
  obtain ⟨X,hX,uX⟩ := actual_two_unit_lift x hx vx
  obtain ⟨Y,hY,uY⟩ := actual_two_unit_lift y hy vy
  have hnonunit : ¬IsUnit (X-Y) := by
    intro hu
    have hz : PadicInt.toZMod (X-Y) ≠ 0 := (hu.map PadicInt.toZMod).ne_zero
    apply hz
    rw [map_sub,actual_unit_residue_two X uX,actual_unit_residue_two Y uY,sub_self]
  have hnorm : ‖x-y‖ < 1 := by
    have h := PadicInt.not_isUnit_iff.mp hnonunit
    simpa only [PadicInt.norm_def,PadicInt.coe_sub,hX,hY] using h
  exact actual_valuation_pos_of_norm_lt_one _ hxy hnorm

lemma actual_unit_square_mod8 (z : ZMod 8) (hz : IsUnit z) : z^2=1 := by
  have hc : Nat.Coprime z.val 8 := (ZMod.isUnit_iff_coprime z.val 8).mp
    (by simpa only [ZMod.natCast_zmod_val] using hz)
  fin_cases z <;> norm_num at hc ⊢

end ActualTwoDescentTwoAdicUnits318
