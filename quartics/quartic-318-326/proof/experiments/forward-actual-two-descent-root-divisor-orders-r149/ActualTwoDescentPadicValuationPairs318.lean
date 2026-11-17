module
public import ActualTwoDescentSimultaneousThreeRoots318
public section
noncomputable section
namespace ActualTwoDescentPadicValuationPairs318
set_option maxHeartbeats 16000000
variable {p : ℕ} [Fact p.Prime]

lemma actual_valuation_neg (x : ℚ_[p]) : (-x).valuation=x.valuation := by
  by_cases hx : x=0
  · simp [hx]
  have hm : (-1 : ℚ_[p]).valuation=0 := by
    have h := Padic.valuation_ratCast (p:=p) (-1)
    norm_num at h
    exact h
  rw [show -x=(-1 : ℚ_[p])*x by ring,Padic.valuation_mul (by norm_num) hx,hm,zero_add]

/-- The exact unequal-value addition rule is derived from the pinned
p-adic valuation triangle inequalities, for actual completed-field values. -/
theorem actual_valuation_add_min (x y : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x+y ≠ 0) (hne : x.valuation ≠ y.valuation) :
    (x+y).valuation=min x.valuation y.valuation := by
  have h1 := Padic.le_valuation_add hxy
  have h2 : min (x+y).valuation y.valuation ≤ x.valuation := by
    have h := Padic.le_valuation_add (x:=x+y) (y:=-y) (by simpa using hx)
    simpa only [actual_valuation_neg,add_neg_cancel_right] using h
  have h3 : min (x+y).valuation x.valuation ≤ y.valuation := by
    have h := Padic.le_valuation_add (x:=x+y) (y:=-x) (by simpa [add_comm,add_left_comm] using hy)
    simpa only [actual_valuation_neg,add_comm x y,add_neg_cancel_right] using h
  omega

/-- A unit difference gives the exact alternatives for the two valuations.
This is an actual Q_p statement, not a formal coefficient condition. -/
theorem actual_unit_difference_pair (x y : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0)
    (hd : x-y ≠ 0) (hv : (x-y).valuation=0) :
    (x.valuation=y.valuation ∧ x.valuation ≤ 0) ∨
    (x.valuation=0 ∧ 0 ≤ y.valuation) ∨
    (0 ≤ x.valuation ∧ y.valuation=0) := by
  have hmin : min x.valuation y.valuation ≤ 0 := by
    have h := Padic.le_valuation_add (x:=x) (y:=-y) (by simpa only [sub_eq_add_neg] using hd)
    simpa only [←sub_eq_add_neg,actual_valuation_neg,hv] using h
  by_cases he : x.valuation=y.valuation
  · exact Or.inl ⟨he,by omega⟩
  · have h := actual_valuation_add_min x (-y) hx (neg_ne_zero.mpr hy)
      (by simpa only [sub_eq_add_neg] using hd) (by simpa only [actual_valuation_neg] using he)
    rw [←sub_eq_add_neg,actual_valuation_neg,hv] at h
    right
    omega

end ActualTwoDescentPadicValuationPairs318
