module
public import ActualPreparedPoleMutualRoots318
public import ActualTwoDescentTwoAdicSquare318
public import ActualTwoDescentTwoAdicUnits318
public import ActualTwoDescentUniformLocalSquare318
public section
noncomputable section
namespace ActualPreparedPoleTwoAdic318
open ActualPreparedPoleSquarefreeClasses318 ActualPreparedPoleLocalSquares318
open ActualPreparedPoleMutualRoots318 ActualTwoDescentTwoAdicUnits318
open ActualTwoDescentLocalValuationTools318

/-- A genuine2-adic root of a positive odd integer forces its residue1
mod8 through the ACTUAL integral reduction map. -/
theorem mod8_of_root (a : ℕ) (ha : 0<a) (ha2 : ¬2∣a)
    (r : ℚ_[2]) (hr : r^2=(a:ℚ_[2])) : (a:ZMod 8)=1 := by
  have ha0 : (a:ℚ_[2])≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt ha)
  have hr0 : r≠0 := by
    intro he
    apply ha0
    simpa only [he,zero_pow (by decide : (2:ℕ)≠0)] using hr.symm
  have hv := congrArg Padic.valuation hr
  rw [Padic.valuation_pow,Padic.valuation_natCast,
    padicValNat.eq_zero_of_not_dvd ha2] at hv
  have vr : r.valuation=0 := by omega
  obtain ⟨R,hR,uR⟩ := actual_two_unit_lift r hr0 vr
  have he : R^2=(a:ℤ_[2]) := by
    apply Subtype.ext
    change (R:ℚ_[2])^2=(a:ℚ_[2])
    rw [hR]
    exact hr
  have hm := congrArg (PadicInt.toZModPow 3) he
  simp only [map_pow,map_natCast] at hm
  have hu := actual_unit_square_mod8 (PadicInt.toZModPow 3 R)
    (uR.map (PadicInt.toZModPow 3))
  exact hm.symm.trans hu

/-- The same beta is a2-adic square:17 is an actual2-adic square,
and the prepared b is an actual2-adic square. -/
theorem beta_root_two {b : ℚ} (C : Classes b) (H : Preparation b) :
    ∃ r : ℚ_[2], r≠0 ∧ r^2=(C.beta:ℚ_[2]) := by
  obtain ⟨u,hu⟩ := ActualTwoDescentTwoAdicSquare318.actual_two_adic_square 17 (by norm_num)
  obtain ⟨v,hv⟩ := H.square_two
  have hv' : v^2=(b:ℚ_[2]) := by simpa only [pow_two] using hv.symm
  apply beta_root C (v/u)
  rw [div_pow,hv',hu]

/-- Depth at least3 gives the strict quarter-neighborhood needed for
Hensel at2, without increasing any local radius or assuming a root. -/
theorem theta_root_two {b : ℚ} (C : Classes b) (H : Preparation b) :
    ∃ r : ℚ_[2], r≠0 ∧ r^2=(C.theta:ℚ_[2]) := by
  letI : Fact (Nat.Prime 17) := ⟨by decide⟩
  let x : ℚ_[2] := (b:ℚ_[2])/17
  have hx0 : x≠0 := div_ne_zero
    (Rat.cast_ne_zero.mpr (ne_of_gt H.positive)) (by norm_num)
  have hxcast : x=((b/17:ℚ):ℚ_[2]) := by simp [x]
  have hvx : 3≤x.valuation := by
    rw [hxcast,Padic.valuation_ratCast,
      padicValRat.div (ne_of_gt H.positive) (by norm_num : (17:ℚ)≠0),
      show (17:ℚ)=((17:ℕ):ℚ) from rfl,padicValRat.of_nat,
      padicValNat_primes (by decide : 2≠17)]
    simpa using H.depth_two
  have hnorm : ‖x‖<(1/4:ℝ) := by
    rw [Padic.norm_eq_zpow_neg_valuation hx0]
    have he : (2:ℝ)^(-x.valuation)<(2:ℝ)^(-2:ℤ) :=
      (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mpr (by omega)
    have hn : (2:ℝ)^(-2:ℤ)=(1/4:ℝ) := by norm_num
    simpa only [hn] using he
  obtain ⟨r,_,hr⟩ := ActualTwoDescentUniformLocalSquare318.actual_quarter_square
    (1-x) (by
      have he : (1-x)-1= -x := by ring
      rw [he,norm_neg]
      exact hnorm)
  exact theta_root C r hr

/-- The actual positive squarefree representatives BOTH equal1 mod8. -/
theorem coefficients_mod8 {b : ℚ} (C : Classes b) (H : Preparation b) :
    (C.beta:ZMod 8)=1 ∧ (C.theta:ZMod 8)=1 := by
  obtain ⟨r,_,hr⟩ := beta_root_two C H
  obtain ⟨s,_,hs⟩ := theta_root_two C H
  exact ⟨mod8_of_root C.beta C.beta_pos (avoid_two_three C H).1 r hr,
    mod8_of_root C.theta C.theta_pos (avoid_two_three C H).2.2.1 s hs⟩

end ActualPreparedPoleTwoAdic318
