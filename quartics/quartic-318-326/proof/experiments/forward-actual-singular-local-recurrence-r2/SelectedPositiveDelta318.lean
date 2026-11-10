module
public import SelectedFormalEntry318
public section
noncomputable section
namespace SelectedPositiveDelta318
open ValuativeOrbitBounds318
set_option maxHeartbeats 1000000

/-- The exact curve equation improves oriented near-identity precision to
four times the u-depth for the UNSQUARED delta. Zero coordinates are allowed. -/
theorem delta_depth {F : Type*} [Field F] (v : AddValuation F (WithTop ℤ))
    (D u y : F) (r : ℤ) (hr : 1≤r) (hD : Bound v 0 D) (h2 : v (2:F)=0)
    (hc : y^2=1-D*u^4) (hn : Near v r u y) : Bound v (4*r) (y-1) := by
  have hdelta : 0<v (y-1) := lt_of_lt_of_le (by exact_mod_cast (show 0<r by omega)) hn.2
  have hplus : v (y+1)=0 := by
    rw [show y+1=(y-1)+2 by ring,
      v.map_add_of_distinct_val (by rw [h2]; exact ne_of_gt hdelta),h2]
    exact min_eq_right hdelta.le
  have hfactor : (y-1)*(y+1)= -(D*u^4) := by linear_combination hc
  have hpow : Bound v (4*r) (u^4) := by
    have h := bsquare v (bsquare v hn.1)
    convert h using 1 <;> ring
  have hb := bneg v (bmul_unit_left v hD hpow)
  have he := congrArg v hfactor
  rw [v.map_mul,hplus,add_zero] at he
  change ((4*r:ℤ):WithTop ℤ)≤v (y-1)
  rw [he]
  exact hb

lemma two_unit (p : ℕ) [Fact p.Prime] (hp : 3≤p) (rho : ℚ_[p]) (hr : rho^2=2) :
    ConcretePadic318.place p rho hr (2:ConcreteG8Domain.K)=0 := by
  have h := ConcretePadic318.rational_nat_unit p 2 (by
    intro hd
    have hle := Nat.le_of_dvd (by norm_num : 0<2) hd
    omega)
  have he : (2:ConcreteG8Domain.K)=ConcreteG8Domain.pair 2 0 := rfl
  rw [he,ConcretePadic318.place_rational]
  exact h

/-- Literal primary charts have u-depth4 and delta-depth16. Literal opposite
charts have u-depth1 and delta-depth4. Both retain original signed labels. -/
theorem original_charts (p : ℕ) [Fact p.Prime] (hp : 3≤p)
    (rho : ℚ_[p]) (hr : rho^2=2) (Pi Mminus Mplus h : ℕ)
    (hpPi : p∣Pi)
    (hminus : SelectedFormalEntry318.Entry p rho hr Mminus)
    (hplus : SelectedFormalEntry318.Entry p (-rho) (ConcretePadic318.negative_root p rho hr) Mplus)
    (hprimary : Nat.ModEq (Pi^3*Mminus) h 0) (hopposite : Nat.ModEq Mplus h 1) (n : ℤ) :
    Bound (ConcretePadic318.place p rho hr) 4 (CoherentMultipleCharts318.chartU (n*(h:ℤ))) ∧
    Bound (ConcretePadic318.place p rho hr) 16 (CoherentMultipleCharts318.chartV (n*(h:ℤ))-1) ∧
    Bound (ConcretePadic318.place p (-rho) (ConcretePadic318.negative_root p rho hr)) 1
      (CoherentMultipleCharts318.chartU (n*((h:ℤ)-1))) ∧
    Bound (ConcretePadic318.place p (-rho) (ConcretePadic318.negative_root p rho hr)) 4
      (CoherentMultipleCharts318.chartV (n*((h:ℤ)-1))-1) := by
  have hm := SelectedFormalEntry318.primary p rho hr Pi Mminus h hpPi hminus hprimary n
  have hp' := SelectedFormalEntry318.opposite p (-rho) (ConcretePadic318.negative_root p rho hr)
    Mplus h hplus hopposite n
  refine ⟨hm.1,?_,hp'.1,?_⟩
  · exact delta_depth _ ConcreteG8Domain.D _ _ 4 (by norm_num)
      (ActualSplitOrbitEntry318.coefficient_bound p rho hr) (two_unit p hp rho hr)
      (CoherentMultipleCharts318.chart_curve _) hm
  · exact delta_depth _ ConcreteG8Domain.D _ _ 1 (by norm_num)
      (ActualSplitOrbitEntry318.coefficient_bound p (-rho) _)
      (two_unit p hp (-rho) _) (CoherentMultipleCharts318.chart_curve _) hp'

end SelectedPositiveDelta318
