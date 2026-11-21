module
public import CTActualDualConnecting318
public import CTGoodOddActualUnitClasses318
public import OriginalCasselsDyadicXClass318
public import OriginalCasselsGoodLift318
import OriginalCasselsOddTargetValuation318
import CTOriginalPadicValuationPairs318
import all CTActualDualConnecting318
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega
public section
noncomputable section

namespace CTActualGoodIsogenyImages318

open ActualTwoDescentSquareClassQuotient318 CTActualDualConnecting318
open ActualTwoDescentEllipticModel318 OriginalSelectedCasselsParity318
open OriginalCasselsDyadicXClass318 OriginalCasselsGoodLift318
open CTGoodOddActualUnitClasses318 OriginalCasselsOddTargetValuation318
open OriginalCasselsOddUnitSquare318 OriginalCasselsOddUnitCharacter318
open ActualTwoDescentLocalValuationTools318 OriginalCasselsRamifiedResidue318
open ActualTwoDescentPadicValuationPairs318

variable {p : ℕ} [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

theorem pdClass_parity (x y : ℚ_[p]) (hx : x≠0) (hy : y≠0)
    (h : classOf x hx=classOf y hy) : x.valuation%2=y.valuation%2 := by
  obtain ⟨r,hr,he⟩ := (class_of_eq_iff _ _ _ _).mp h
  have he' := congrArg Padic.valuation he
  rw [Padic.valuation_mul hy (pow_ne_zero 2 hr),Padic.valuation_pow] at he'
  omega

private theorem pdUnitValue (b : ℕ) (hb : ¬p∣b) : ((b:ℚ_[p])).valuation=0 :=
  actual_prime_unit_valuation b hb

private theorem goodTargetVal (hp : 5≤p) (N : ℤ_[p]) (hN : IsUnit N)
    (x y : ℚ_[p]) (hx : x≠0)
    (hE : y^2=x*(x^2-4*(N:ℚ_[p])*x+16*(N:ℚ_[p])^2)) :
    x.valuation%2=0 := by
  by_cases h : x.valuation=0
  · simp [h]
  have hN0 : (N:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hN.ne_zero
  have hFour : (4:ℚ_[p]).valuation=0 := by
    simpa only [Nat.cast_ofNat] using (pdUnitValue (p:=p) 4
      (fun hd => (by omega : ¬p≤4) (Nat.le_of_dvd (by decide : 0<4) hd)))
  have hNVal := actual_val_zero_of_unit N hN
  have hv : ((4:ℚ_[p])*(N:ℚ_[p])).valuation=0 := by
    rw [Padic.valuation_mul (by norm_num : (4:ℚ_[p])≠0) hN0,hFour,hNVal,add_zero]
  obtain ⟨u,hu,hSq⟩ := abscissa_square_of_factor_square (N:ℚ_[p]) x y hx hE
    (factor_square_of_unequal_val (by omega : p≠2) _ _ hN0 hx (fun e => h (e.trans hv)))
  have hVal := congrArg Padic.valuation hSq
  rw [Padic.valuation_pow] at hVal
  omega

/-- At an actual omitted good prime the forward local scalar image is
exactly the even-valuation squareclasses. Both directions quantify over
the true quotient curve points. -/
theorem target_good_class_iff (hp : 5≤p) (N : ℤ_[p]) (hN : IsUnit N)
    (a : ℚ_[p]) (ha : a≠0) :
    (∃ P : TargetPoint (N:ℚ_[p]), targetClass P=classOf a ha) ↔ a.valuation%2=0 := by
  let n : ℚ_[p] := N
  have hn : n≠0 := PadicInt.coe_ne_zero.mpr hN.ne_zero
  have hp2 : p≠2 := by omega
  constructor
  · rintro ⟨P,hP⟩
    cases P with
    | zero =>
      change 1=classOf a ha at hP
      rw [←class_of_one] at hP
      simpa only [Padic.valuation_one,Int.zero_emod] using pdClass_parity a 1 ha one_ne_zero hP.symm
    | some x y w =>
      by_cases hx : x=0
      · have hOne : 1=classOf a ha := by simpa only [targetClass,dif_pos hx] using hP
        rw [←class_of_one] at hOne
        simpa only [Padic.valuation_one,Int.zero_emod] using pdClass_parity a 1 ha one_ne_zero hOne.symm
      have he := w.left
      rw [WeierstrassCurve.Affine.equation_iff] at he
      simp only [targetModel,zero_mul,add_zero,zero_add] at he
      have hE : y^2=x*(x^2-4*n*x+16*n^2) := by linear_combination he
      change targetClass (targetPoint n x y hn hE)=classOf a ha at hP
      rw [target_class_at_affine hn hx hE] at hP
      exact (pdClass_parity a x ha hx hP.symm).trans (goodTargetVal hp N hN x y hx hE)
  · intro hV
    obtain ⟨U,hU,hA⟩ := even_valuation_has_unit a ha hV
    have hU0 : (U:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hU.ne_zero
    by_cases hS : IsSquare (PadicInt.toZMod U)
    · obtain ⟨r,hr,he⟩ := (unit_square_iff_residue hp2 U hU).mp hS
      have hOne : classOf (U:ℚ_[p]) hU0=1 := by
        rw [←class_of_one]
        exact (class_of_eq_iff _ _ _ _).mpr ⟨r,hr,by simpa only [one_mul] using he⟩
      exact ⟨0,(hA.trans hOne).symm⟩
    obtain ⟨X,Y,hX,hXS,hE⟩ := exists_lifted_nonsquare_abscissa hp N hN
    obtain ⟨r,hr,hR⟩ := unit_ratio_square_of_nonsquare hp2 U X hU hX hS hXS
    have hX0 : (X:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hX.ne_zero
    have hE' : (Y:ℚ_[p])^2=(X:ℚ_[p])*((X:ℚ_[p])^2-4*n*(X:ℚ_[p])+16*n^2) := by
      have hc := congrArg (algebraMap ℤ_[p] ℚ_[p]) hE
      simpa only [n,map_pow,map_mul,map_add,map_sub,map_ofNat,PadicInt.algebraMap_apply] using hc
    refine ⟨targetPoint n (X:ℚ_[p]) (Y:ℚ_[p]) hn hE',?_⟩
    rw [target_class_at_affine hn hX0 hE']
    exact (hA.trans ((class_of_eq_iff _ _ hU0 hX0).mpr ⟨r,hr,hR⟩)).symm

/-- The same even-valuation line is the actual reverse image,
with the exceptional source kernel scalar `-3 n²`, not x=0. -/
theorem source_good_class_iff (hp : 5≤p) (N : ℤ_[p]) (hN : IsUnit N)
    (a : ℚ_[p]) (ha : a≠0) :
    let hn := PadicInt.coe_ne_zero.mpr hN.ne_zero
    (∃ P : Point (N:ℚ_[p]), reverseValue ℚ_[p] (N:ℚ_[p]) hn P=classOf a ha) ↔ a.valuation%2=0 := by
  let n : ℚ_[p] := N
  let hn : n≠0 := PadicInt.coe_ne_zero.mpr hN.ne_zero
  change (∃ P : Point n, reverseValue ℚ_[p] n hn P=classOf a ha) ↔ a.valuation%2=0
  constructor
  · rintro ⟨P,hP⟩
    cases P with
    | zero =>
      change 1=classOf a ha at hP
      rw [←class_of_one] at hP
      simpa only [Padic.valuation_one,Int.zero_emod] using pdClass_parity a 1 ha one_ne_zero hP.symm
    | some x y w =>
      by_cases hx : x=0
      · simp only [reverseValue,dif_pos hx] at hP
        have hp3 : (3:ℚ_[p]).valuation=0 := by
          simpa only [Nat.cast_ofNat] using (pdUnitValue (p:=p) 3
            (fun hd => (by omega : ¬p≤3) (Nat.le_of_dvd (by decide : 0<3) hd)))
        have hv := pdClass_parity a (-3*n^2) ha (exceptional_scalar_ne ℚ_[p] n hn) hP.symm
        rw [Padic.valuation_mul (by norm_num : (-3:ℚ_[p])≠0) (pow_ne_zero 2 hn),
          actual_valuation_neg,hp3,Padic.valuation_pow,zero_add] at hv
        omega
      simp only [reverseValue,dif_neg hx] at hP
      have hE := (curve_equation n x y).mp w.left
      exact (pdClass_parity a x ha hx hP.symm).trans (source_affine_even_valuation hp N hN x y hx hE)
  · intro hV
    obtain ⟨U,hU,hA⟩ := even_valuation_has_unit a ha hV
    rcases good_unit_class_occurs hp N U hN hU with hOne|⟨X,Y,hX,hE,hC⟩
    · exact ⟨0,(hA.trans hOne).symm⟩
    have hx : (X:ℚ_[p])≠0 := PadicInt.coe_ne_zero.mpr hX.ne_zero
    have hE' : (Y:ℚ_[p])^2=(X:ℚ_[p])*((X:ℚ_[p])-n)*((X:ℚ_[p])+3*n) := by
      simpa only [n,map_pow,map_mul,map_add,map_sub,map_ofNat,PadicInt.algebraMap_apply] using
        congrArg (algebraMap ℤ_[p] ℚ_[p]) hE
    refine ⟨point n (X:ℚ_[p]) (Y:ℚ_[p]) hn hE',?_⟩
    unfold point
    simpa only [reverseValue,dif_neg hx] using (hA.trans hC).symm

end CTActualGoodIsogenyImages318

#print axioms CTActualGoodIsogenyImages318.target_good_class_iff
#print axioms CTActualGoodIsogenyImages318.source_good_class_iff
