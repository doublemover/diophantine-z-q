module
public import ActualTwoDescentTwoAdicUnits318
public import ActualTwoDescentHenselSquare318
public import ActualTwoDescentLocalValuationTools318
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.LinearCombination
public section

noncomputable section

namespace OriginalCasselsDyadicNormalize318

open ActualTwoDescentTwoAdicUnits318 ActualTwoDescentHenselSquare318
open ActualTwoDescentLocalValuationTools318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

@[expose] def res8 : ℤ_[2] →+* ZMod 8 := PadicInt.toZModPow 3

theorem integral_of_nonnegative_val (x : ℚ_[2]) (hx : 0 ≤ x.valuation) :
    ∃ U : ℤ_[2], (U:ℚ_[2])=x :=
  ⟨⟨x,(Padic.norm_le_one_iff_val_nonneg x).mpr hx⟩,rfl⟩

theorem val_pow_two (j : ℤ) : ((2:ℚ_[2])^j).valuation=j := by
  rw [Padic.valuation_zpow,show (2:ℚ_[2]).valuation=1 from Padic.valuation_p,mul_one]

theorem actual_unit_normal (x : ℚ_[2]) (hx : x ≠ 0) (j : ℤ) (hj : x.valuation=j) :
    ∃ U : ℤ_[2], IsUnit U ∧ x=(2:ℚ_[2])^j*(U:ℚ_[2]) := by
  have h2 : (2 : ℚ_[2]) ≠ 0 := by norm_num
  have hd : (2:ℚ_[2])^j ≠ 0 := zpow_ne_zero j h2
  have hV : (x/(2:ℚ_[2])^j).valuation=0 := by
    rw [actual_valuation_div _ _ hx hd, hj, val_pow_two, sub_self]
  obtain ⟨U,hU,uU⟩ := actual_two_unit_lift _ (div_ne_zero hx hd) hV
  refine ⟨U,uU,?_⟩
  rw [hU]
  field_simp [hd] <;> ring

theorem unit_of_mod2_one (U : ℤ_[2]) (hU : PadicInt.toZMod U=1) : IsUnit U := by
  by_contra h
  obtain ⟨V,hV⟩ := (PadicInt.norm_lt_one_iff_dvd U).mp (PadicInt.not_isUnit_iff.mp h)
  rw [hV,map_mul,map_ofNat,show (2:ZMod 2)=0 by decide,zero_mul] at hU
  exact (by decide : (0:ZMod 2) ≠ 1) hU

theorem val_of_unit (U : ℤ_[2]) (hU : IsUnit U) : (U:ℚ_[2]).valuation=0 := by
  have hz : (U:ℚ_[2])≠0 := PadicInt.coe_ne_zero.mpr hU.ne_zero
  have hn : ‖(U:ℚ_[2])‖=(1:ℝ) := PadicInt.isUnit_iff.mp hU
  rw [Padic.norm_eq_zpow_neg_valuation hz,← zpow_zero (2:ℝ)] at hn
  have he := (zpow_right_strictMono₀ (by norm_num : (1:ℝ)<2)).injective hn
  omega

/-- Unit square lifting for arbitrary actual 2-adic integers, not just
the natural-integer special case. -/
theorem square_of_res8_one (A : ℤ_[2]) (ha : res8 A=1) :
    ∃ u : ℚ_[2], u ≠ 0 ∧ u^2=(A:ℚ_[2]) := by
  have hk : 1-A ∈ RingHom.ker (PadicInt.toZModPow (p:=2) 3) := by
    apply RingHom.mem_ker.mpr
    change res8 (1-A)=0
    rw [map_sub,map_one,ha,sub_self]
  rw [PadicInt.ker_toZModPow] at hk
  have hclose := (PadicInt.norm_le_pow_iff_mem_span_pow (1-A) 3).mpr hk
  have hderiv : ‖(2 : ℤ_[2])*1‖^2=(1/4 : ℝ) := by
    rw [mul_one,PadicInt.norm_p]
    norm_num
  obtain ⟨u,hu⟩ := actual_hensel_square A 1 (by
    rw [one_pow,hderiv]
    exact lt_of_le_of_lt hclose (by norm_num))
  have ha0 : A ≠ 0 := by
    intro h
    rw [h,map_zero] at ha
    exact (by decide : (0:ZMod 8)≠1) ha
  have hu0 : u ≠ 0 := by
    intro h
    rw [h,zero_pow (by decide : (2:ℕ)≠0)] at hu
    exact ha0 hu.symm
  exact ⟨(u:ℚ_[2]),PadicInt.coe_ne_zero.mpr hu0,by exact_mod_cast hu⟩

theorem five_square_of_res8_five (A : ℤ_[2]) (ha : res8 A=5) :
    ∃ u : ℚ_[2], u ≠ 0 ∧ (A:ℚ_[2])=5*u^2 := by
  have hB : res8 (5*A)=1 := by
    rw [map_mul,map_ofNat,ha] <;> decide
  obtain ⟨s,hs,hS⟩ := square_of_res8_one (5*A) hB
  have h5 : (5:ℚ_[2]) ≠ 0 := by norm_num
  refine ⟨s/5,div_ne_zero hs h5,?_⟩
  change s^2 = (5:ℚ_[2])*(A:ℚ_[2]) at hS
  rw [div_pow,hS]
  ring

/-- Exact unit-square restriction after scaling by the true signed
power of 2. In particular its valuation cannot be an odd integer. -/
theorem square_scaled_unit (A : ℤ_[2]) (hA : IsUnit A) (j : ℤ) (y : ℚ_[2])
    (he : y^2=(2:ℚ_[2])^j*(A:ℚ_[2])) :
    j=2*y.valuation ∧ res8 A=1 := by
  have h2 : (2:ℚ_[2])≠0 := by norm_num
  have hA0 : (A:ℚ_[2])≠0 := PadicInt.coe_ne_zero.mpr hA.ne_zero
  have hy : y≠0 := by
    intro hz
    rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at he
    exact (mul_ne_zero (zpow_ne_zero _ h2) hA0) he.symm
  have hv := congrArg Padic.valuation he
  rw [Padic.valuation_pow,Padic.valuation_mul (zpow_ne_zero _ h2) hA0,
    val_pow_two,val_of_unit A hA,add_zero] at hv
  have hj : j=2*y.valuation := by omega
  refine ⟨hj,?_⟩
  obtain ⟨U,hU,hu⟩ := actual_unit_normal y hy y.valuation rfl
  have hs : y^2=(2:ℚ_[2])^j*(U:ℚ_[2])^2 := by
    calc
      _ = ((2:ℚ_[2])^y.valuation*(U:ℚ_[2]))^2 := congrArg (fun t : ℚ_[2] => t^2) hu
      _ = _ := by
        have ha : j=y.valuation+y.valuation := by omega
        rw [ha,zpow_add₀ h2]
        ring
  have hsu := mul_left_cancel₀ (zpow_ne_zero j h2) (hs.symm.trans he)
  have hsu' : U^2=A := by
    apply PadicInt.ext
    simpa only [PadicInt.coe_pow] using hsu
  have hf := congrArg res8 hsu'
  rw [map_pow,actual_unit_square_mod8 _ (hU.map res8)] at hf
  exact hf.symm

end OriginalCasselsDyadicNormalize318

#print axioms OriginalCasselsDyadicNormalize318.square_of_res8_one
#print axioms OriginalCasselsDyadicNormalize318.square_scaled_unit
