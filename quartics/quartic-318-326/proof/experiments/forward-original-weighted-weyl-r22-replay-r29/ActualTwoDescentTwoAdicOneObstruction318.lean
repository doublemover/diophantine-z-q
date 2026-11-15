module
public import ActualTwoDescentModEightObstruction318
public section
noncomputable section
namespace ActualTwoDescentTwoAdicOneObstruction318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentLocalValuationTools318
open ActualTwoDescentTwoAdicUnits318 ActualTwoDescentModEightObstruction318
set_option maxHeartbeats 16000000

/-- The problematic valuation1 case is excluded for ACTUAL Q_2 curve
points by lifting y/2 and(x-n)/2 to integral units and reducing the exact
cubic modulo8. No residue condition is inserted as an assumption. -/
theorem actual_two_valuation_one_impossible (n : ℕ) (hn : n%4=3)
    (P : LocalPoint (p:=2) n) (hx : P.x.valuation=0)
    (hB : (P.x-n).valuation=1) (hA : (P.x+3*n).valuation=1) : False := by
  have hy : P.y ≠ 0 := by
    intro he
    have h := P.curve
    rw [he,zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact (mul_ne_zero (mul_ne_zero P.x_ne P.minus_ne) P.plus_ne) h.symm
  have hcurve := congrArg Padic.valuation P.curve
  rw [Padic.valuation_pow,Padic.valuation_mul (mul_ne_zero P.x_ne P.minus_ne) P.plus_ne,
    Padic.valuation_mul P.x_ne P.minus_ne,hx,hB,hA] at hcurve
  have hvy : P.y.valuation=1 := by omega
  let u : ℚ_[2] := (P.x-n)/2
  let w : ℚ_[2] := P.y/2
  have hu0 : u ≠ 0 := div_ne_zero P.minus_ne (by norm_num)
  have hw0 : w ≠ 0 := div_ne_zero hy (by norm_num)
  have hvu : u.valuation=0 := by
    rw [u,actual_valuation_div _ _ P.minus_ne (by norm_num),hB,Padic.valuation_p,sub_self]
  have hvw : w.valuation=0 := by
    rw [w,actual_valuation_div _ _ hy (by norm_num),hvy,Padic.valuation_p,sub_self]
  have heB : P.x-n=2*u := by dsimp [u]; field_simp; ring
  have heX : P.x=(n : ℚ_[2])+2*u := by rw [←heB]; ring
  have heA : P.x+3*n=2*(u+2*n) := by rw [heX]; ring
  have he : w^2=((n : ℚ_[2])+2*u)*u*(u+2*n) := by
    dsimp [w]
    rw [div_pow,P.curve,heB,heA,heX]
    field_simp
    <;> ring
  obtain ⟨U,hU,uU⟩ := actual_two_unit_lift u hu0 hvu
  obtain ⟨W,hW,uW⟩ := actual_two_unit_lift w hw0 hvw
  have heZ : W^2=((n : ℤ_[2])+2*U)*U*(U+2*n) := by
    apply Subtype.ext
    change (W : ℚ_[2])^2=((n : ℚ_[2])+2*(U : ℚ_[2]))*(U : ℚ_[2])*((U : ℚ_[2])+2*n)
    rw [hU,hW]
    exact he
  exact actual_two_unit_cubic_obstruction n hn U W uU uW heZ

end ActualTwoDescentTwoAdicOneObstruction318
