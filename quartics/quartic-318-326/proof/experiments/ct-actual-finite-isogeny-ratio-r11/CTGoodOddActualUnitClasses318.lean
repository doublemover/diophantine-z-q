module
public import CTGoodOddActualSourceLift318
public import ActualTwoDescentSquareClassQuotient318
import CTOriginalPadicValuationPairs318
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section

noncomputable section

namespace CTGoodOddActualUnitClasses318

open CTGoodOddActualSourceLift318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentLocalValuationTools318 ActualTwoDescentPadicValuationPairs318
open OriginalCasselsOddUnitCharacter318 OriginalCasselsOddUnitSquare318
open OriginalCasselsRamifiedResidue318

variable {p : ℕ} [Fact p.Prime]

private theorem valuation_add_unit (x b : ℚ_[p]) (hx : x≠0) (hb : b≠0)
    (hv : x.valuation≠0) (hbv : b.valuation=0) :
    x+b≠0 ∧ (x+b).valuation=min x.valuation 0 := by
  have h0 : x+b≠0 := by
    intro h
    exact hv (by rw [eq_neg_of_add_eq_zero_left h,actual_valuation_neg,hbv])
  exact ⟨h0,(actual_valuation_add_min x b hx hb h0 (by rwa [hbv])).trans
    (congrArg (min x.valuation) hbv)⟩

/-- Good odd source x-values are actually unramified classes. The two
unequal-valuation factors are both compared against unit shifts. -/
theorem source_affine_even_valuation (hp : 5≤p) (N : ℤ_[p]) (hN : IsUnit N)
    (x y : ℚ_[p]) (hx : x≠0)
    (he : y^2=x*(x-(N:ℚ_[p]))*(x+3*(N:ℚ_[p]))) :
    x.valuation%2=0 := by
  by_cases hv : x.valuation=0
  · simp [hv]
  have hn : (N:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hN.ne_zero
  have hvn := actual_val_zero_of_unit N hN
  have h3 : (3:ℚ_[p])≠0 := by norm_num
  have h3v : (3:ℚ_[p]).valuation=0 := by
    change ((3:ℕ):ℚ_[p]).valuation=0
    apply actual_prime_unit_valuation
    exact fun hd => (by omega : ¬p≤3) (Nat.le_of_dvd (by decide : 0<3) hd)
  have h3n : (3*(N:ℚ_[p])).valuation=0 := by
    rw [Padic.valuation_mul h3 hn,h3v,hvn,zero_add]
  obtain ⟨hL,hLv⟩ := valuation_add_unit x (-(N:ℚ_[p])) hx (neg_ne_zero.mpr hn) hv
    ((actual_valuation_neg _).trans hvn)
  obtain ⟨hR,hRv⟩ := valuation_add_unit x (3*(N:ℚ_[p])) hx (mul_ne_zero h3 hn) hv h3n
  rw [←sub_eq_add_neg] at hL hLv
  have hVal := congrArg Padic.valuation he
  rw [Padic.valuation_pow,Padic.valuation_mul (mul_ne_zero hx hL) hR,
    Padic.valuation_mul hx hL,hLv,hRv] at hVal
  by_cases hl : x.valuation≤0
  · rw [min_eq_left hl] at hVal
    omega
  · rw [min_eq_right (by omega : 0≤x.valuation)] at hVal
    omega

/-- Every even-valuation class has an actual unit representative. -/
theorem even_valuation_has_unit (x : ℚ_[p]) (hx : x≠0) (hv : x.valuation%2=0) :
    ∃ A : ℤ_[p], ∃ hA : IsUnit A,
      classOf x hx=classOf (A:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hA.ne_zero) := by
  obtain ⟨A,hA,hxA⟩ := actual_odd_unit_normal x hx
  let k := x.valuation/2
  have hk : x.valuation=k+k := by dsimp [k]; omega
  have hp0 : (p:ℚ_[p])≠0 := Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime p).ne_zero
  refine ⟨A,hA,(class_of_eq_iff _ _ _ _).mpr ?_⟩
  refine ⟨(p:ℚ_[p])^k,zpow_ne_zero k hp0,?_⟩
  calc
    x=(p:ℚ_[p])^(k+k)*(A:ℚ_[p]) := by rw [←hk]; exact hxA
    _=(A:ℚ_[p])*((p:ℚ_[p])^k)^2 := by
      rw [zpow_add₀ hp0,pow_two]
      ac_rfl

/-- Every actual unit class at a good omitted prime occurs on the source:
the trivial class at O, and any nonsquare one on the same lifted affine
point. The receiver gets the actual squareclass equality. -/
theorem good_unit_class_occurs (hp : 5≤p) (N A : ℤ_[p]) (hN : IsUnit N) (hA : IsUnit A) :
    classOf (A:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hA.ne_zero)=1 ∨
      ∃ x y : ℤ_[p], ∃ hx : IsUnit x,
        y^2=x*(x-N)*(x+3*N) ∧
          classOf (A:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hA.ne_zero)=
            classOf (x:ℚ_[p]) (PadicInt.coe_ne_zero.mpr hx.ne_zero) := by
  have hp2 : p≠2 := by omega
  by_cases hS : IsSquare (PadicInt.toZMod A)
  · left
    obtain ⟨r,hr,he⟩ := (unit_square_iff_residue hp2 A hA).mpr hS
    rw [←class_of_one]
    exact (class_of_eq_iff _ _ _ _).mpr ⟨r,hr,by simpa only [one_mul] using he⟩
  · right
    obtain ⟨x,y,hx,hNS,hY⟩ := exists_good_source_nonsquare_unit hp N hN
    obtain ⟨r,hr,he⟩ := unit_ratio_square_of_nonsquare hp2 A x hA hx hS hNS
    exact ⟨x,y,hx,hY,(class_of_eq_iff _ _ _ _).mpr ⟨r,hr,he⟩⟩

end CTGoodOddActualUnitClasses318

#print axioms CTGoodOddActualUnitClasses318.source_affine_even_valuation
#print axioms CTGoodOddActualUnitClasses318.good_unit_class_occurs
