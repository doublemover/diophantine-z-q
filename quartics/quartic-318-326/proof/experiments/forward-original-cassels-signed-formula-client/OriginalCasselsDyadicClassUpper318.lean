module
public import OriginalCasselsDyadicXClass318
public import OriginalCasselsDyadicNormalize318
public import OriginalSelectedCasselsLocalArithmetic318
public import Mathlib.Tactic.FinCases
import all OriginalSelectedCasselsParity318
public section

noncomputable section

namespace OriginalCasselsDyadicClassUpper318

open OriginalCasselsDyadicXClass318 OriginalCasselsDyadicNormalize318
open OriginalSelectedCasselsLocalArithmetic318 OriginalSelectedCasselsParity318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentTwoAdicUnits318
open ActualTwoDescentLocalValuationTools318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : DecidableEq (ℚ_[2]) := Classical.decEq _

private def g (n x : ℚ_[2]) : ℚ_[2] := x^2-4*n*x+16*n^2

private theorem class_of_factor {n x y d u : ℚ_[2]}
    (hx : x ≠ 0) (hd : d ≠ 0) (hu : u ≠ 0)
    (hy : y^2=x*g n x) (hg : g n x=d*u^2) :
    classOf x hx=classOf d hd := by
  rw [hg] at hy
  have hy0 : y ≠ 0 := by
    intro ht
    rw [ht,zero_pow (by decide : (2:ℕ)≠0)] at hy
    exact (mul_ne_zero hx (mul_ne_zero hd (pow_ne_zero _ hu))) hy.symm
  apply (class_of_eq_iff x d hx hd).mpr
  refine ⟨y/(d*u), div_ne_zero hy0 (mul_ne_zero hd hu),?_⟩
  calc
    x = y^2/(d*u^2) := ((div_eq_iff (mul_ne_zero hd (pow_ne_zero _ hu))).mpr hy).symm
    _ = d*(y/(d*u))^2 := by field_simp [hd,hu] <;> ring

private theorem selected_residues (n : ℕ) (hr : (n:ZMod 12)=11) :
    (n:ZMod 2)=1 ∧ ((n:ZMod 8)=3 ∨ (n:ZMod 8)=7) := by
  have h12 : n%12=11 := by
    have h := congrArg ZMod.val hr
    norm_num only [ZMod.val_natCast] at h
    exact h
  have h24 : n%24=11 ∨ n%24=23 := by
    have hm := (Nat.mod_mod_of_dvd n (by decide : 12 ∣ 24)).trans h12
    have hl := Nat.mod_lt n (by decide : 0<24)
    omega
  constructor
  · apply (ZMod.natCast_eq_natCast_iff' n 1 2).mpr
    rw [← Nat.mod_mod_of_dvd n (by decide : 2 ∣ 12), h12]
  · have h8 : (n:ZMod 8) = ((n%24 : ℕ):ZMod 8) :=
      (ZMod.natCast_eq_natCast_iff' n (n%24) 8).mpr
        (Nat.mod_mod_of_dvd n (by decide : 8 ∣ 24)).symm
    rw [h8]
    rcases h24 with h | h <;> rw [h] <;> decide

private theorem residue8_unit_cases (U : ℤ_[2]) (hU : IsUnit U) :
    res8 U=1 ∨ res8 U=3 ∨ res8 U=5 ∨ res8 U=7 := by
  have hC : Nat.Coprime (res8 U).val 8 :=
    (ZMod.isUnit_iff_coprime _ 8).mp
      (by simpa only [ZMod.natCast_zmod_val] using hU.map res8)
  have htable : ∀ t : Fin 8, Nat.Coprime t.val 8 →
      ((t.val : ℕ) : ZMod 8) = 1 ∨ ((t.val : ℕ) : ZMod 8) = 3 ∨
      ((t.val : ℕ) : ZMod 8) = 5 ∨ ((t.val : ℕ) : ZMod 8) = 7 := by decide
  simpa only [ZMod.natCast_zmod_val] using
    htable ⟨(res8 U).val,ZMod.val_lt (res8 U)⟩ hC

private theorem far_norm (B : ℤ_[2]) :
    ∃ u : ℚ_[2], u ≠ 0 ∧ (1 : ℚ_[2])-8*(B:ℚ_[2])+64*(B:ℚ_[2])^2=u^2 := by
  let C : ℤ_[2] := 1-8*B+64*B^2
  have hC : res8 C=1 := by
    simp only [C,map_add,map_sub,map_mul,map_pow,map_one,map_ofNat]
    simp [show (8:ZMod 8)=0 by decide,show (64:ZMod 8)=0 by decide]
  obtain ⟨u,hu,he⟩ := square_of_res8_one C hC
  exact ⟨u,hu,he.symm⟩

private theorem square_factor_low {n : ℕ} {x : ℚ_[2]} (hx : x ≠ 0)
    (hv : x.valuation<0) :
    ∃ u : ℚ_[2], u ≠ 0 ∧ g n x=(1:ℚ_[2])*u^2 := by
  have h2 : (2:ℚ_[2]) ≠ 0 := by norm_num
  have hV : 0 ≤ (x⁻¹/(2:ℚ_[2])).valuation := by
    rw [actual_valuation_div _ _ (inv_ne_zero hx) h2,Padic.valuation_inv,
      show (2:ℚ_[2]).valuation=1 from Padic.valuation_p]
    omega
  obtain ⟨B,hB⟩ := integral_of_nonnegative_val _ hV
  obtain ⟨s,hs,hS⟩ := far_norm ((n:ℤ_[2])*B)
  refine ⟨x*s,mul_ne_zero hx hs,?_⟩
  change 1-8*((n:ℚ_[2])*(B:ℚ_[2]))+64*((n:ℚ_[2])*(B:ℚ_[2]))^2=s^2 at hS
  rw [g,mul_pow,←hS,hB]
  field_simp [hx] <;> ring

private theorem square_factor_high {n : ℕ} (hn : 0<n) (hodd : (n:ZMod 2)=1)
    {x : ℚ_[2]} (hx : x ≠ 0) (hv : 5≤x.valuation) :
    ∃ u : ℚ_[2], u ≠ 0 ∧ g n x=(1:ℚ_[2])*u^2 := by
  have hn0 : (n:ℚ_[2])≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hndvd : ¬2∣n := by
    intro hh
    have he := (ZMod.natCast_eq_zero_iff n 2).mpr hh
    rw [hodd] at he
    exact one_ne_zero he
  have h32 : (32:ℚ_[2])≠0 := by norm_num
  have h32v : (32:ℚ_[2]).valuation=5 := by
    rw [show (32:ℚ_[2])=(2:ℚ_[2])^(5:ℤ) by norm_num,val_pow_two]
  have hV : 0 ≤ (x/(32*(n:ℚ_[2]))).valuation := by
    rw [actual_valuation_div _ _ hx (mul_ne_zero h32 hn0),
      Padic.valuation_mul h32 hn0,h32v,actual_prime_unit_valuation n hndvd,add_zero]
    omega
  obtain ⟨B,hB⟩ := integral_of_nonnegative_val _ hV
  obtain ⟨s,hs,hS⟩ := far_norm B
  refine ⟨4*(n:ℚ_[2])*s,mul_ne_zero (mul_ne_zero (by norm_num) hn0) hs,?_⟩
  rw [g,mul_pow,←hS,hB]
  field_simp [hn0] <;> ring

private theorem five_factor_zero {n : ℕ} (hn8 : (n:ZMod 8)=3 ∨ (n:ZMod 8)=7)
    {x : ℚ_[2]} (hx : x ≠ 0) (hv : x.valuation=0) :
    ∃ u : ℚ_[2], u ≠ 0 ∧ g n x=(5:ℚ_[2])*u^2 := by
  obtain ⟨U,hU,hxU⟩ := actual_unit_normal x hx 0 hv
  simp only [zpow_zero,one_mul] at hxU
  let A : ℤ_[2] := U^2-4*n*U+16*n^2
  have ha : res8 A=5 := by
    simp only [A,map_add,map_sub,map_mul,map_pow,map_natCast,map_ofNat]
    exact (dyadic_unit_rows _ _ hn8 (residue8_unit_cases U hU)).1
  obtain ⟨s,hs,hS⟩ := five_square_of_res8_five A ha
  exact ⟨s,hs,by rw [g,hxU]; exact hS⟩

private theorem five_factor_four {n : ℕ} (hn8 : (n:ZMod 8)=3 ∨ (n:ZMod 8)=7)
    {x : ℚ_[2]} (hx : x ≠ 0) (hv : x.valuation=4) :
    ∃ u : ℚ_[2], u ≠ 0 ∧ g n x=(5:ℚ_[2])*u^2 := by
  obtain ⟨U,hU,hxU⟩ := actual_unit_normal x hx 4 hv
  have hxU' : x=16*(U:ℚ_[2]) := by
    rw [show (16:ℚ_[2])=(2:ℚ_[2])^(4:ℤ) by norm_num]
    exact hxU
  let A : ℤ_[2] := 16*U^2-4*n*U+n^2
  have ha : res8 A=5 := by
    simp only [A,map_add,map_sub,map_mul,map_pow,map_natCast,map_ofNat]
    exact (dyadic_unit_rows _ _ hn8 (residue8_unit_cases U hU)).2.2
  obtain ⟨s,hs,hS⟩ := five_square_of_res8_five A ha
  refine ⟨4*s,mul_ne_zero (by norm_num) hs,?_⟩
  calc
    _ = 16*(A:ℚ_[2]) := by
      rw [g,hxU']
      dsimp [A]
      push_cast
      have hc4 : ((4 : ℤ_[2]) : ℚ_[2]) = 4 := by
        change PadicInt.Coe.ringHom (4 : ℤ_[2]) = (4 : ℚ_[2])
        exact map_ofNat PadicInt.Coe.ringHom 4
      have hc16 : ((16 : ℤ_[2]) : ℚ_[2]) = 16 := by
        change PadicInt.Coe.ringHom (16 : ℤ_[2]) = (16 : ℚ_[2])
        exact map_ofNat PadicInt.Coe.ringHom 16
      simp only [hc4,hc16]
      ring
    _ = _ := by rw [hS]; ring

private theorem valuation_one_impossible {n : ℕ} (hn2 : (n:ZMod 2)=1)
    {x y : ℚ_[2]} (hx : x ≠ 0) (hv : x.valuation=1) (hy : y^2=x*g n x) : False := by
  obtain ⟨U,hU,hxU⟩ := actual_unit_normal x hx 1 hv
  rw [zpow_one] at hxU
  let A : ℤ_[2] := U*(U^2-2*n*U+4*n^2)
  have ha : PadicInt.toZMod A=1 := by
    simp only [A,map_add,map_sub,map_mul,map_pow,map_natCast,map_ofNat,
      actual_unit_residue_two U hU,hn2] <;> decide
  have hY : y^2=(2:ℚ_[2])^(3:ℤ)*(A:ℚ_[2]) := by
    rw [hy,g,hxU]
    dsimp [A]
    push_cast
    rw [show (2:ℚ_[2])^(3:ℤ)=8 by norm_num]
    have hc2 : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by
      change PadicInt.Coe.ringHom (2 : ℤ_[2]) = (2 : ℚ_[2])
      exact map_ofNat PadicInt.Coe.ringHom 2
    have hc4 : ((4 : ℤ_[2]) : ℚ_[2]) = 4 := by
      change PadicInt.Coe.ringHom (4 : ℤ_[2]) = (4 : ℚ_[2])
      exact map_ofNat PadicInt.Coe.ringHom 4
    simp only [hc2,hc4]
    ring
  have hv' := (square_scaled_unit A (unit_of_mod2_one A ha) 3 y hY).1
  omega

private theorem valuation_two_impossible {n : ℕ} (hn2 : (n:ZMod 2)=1)
    (hn8 : (n:ZMod 8)=3 ∨ (n:ZMod 8)=7)
    {x y : ℚ_[2]} (hx : x ≠ 0) (hv : x.valuation=2) (hy : y^2=x*g n x) : False := by
  obtain ⟨U,hU,hxU⟩ := actual_unit_normal x hx 2 hv
  have hxU' : x=4*(U:ℚ_[2]) := by
    rw [show (4:ℚ_[2])=(2:ℚ_[2])^(2:ℤ) by norm_num]
    exact hxU
  let A : ℤ_[2] := U*(U^2-n*U+n^2)
  have ha : PadicInt.toZMod A=1 := by
    simp only [A,map_add,map_sub,map_mul,map_pow,map_natCast,map_ofNat,
      actual_unit_residue_two U hU,hn2] <;> decide
  have hY : y^2=(2:ℚ_[2])^(6:ℤ)*(A:ℚ_[2]) := by
    rw [hy,g,hxU']
    dsimp [A]
    push_cast
    rw [show (2:ℚ_[2])^(6:ℤ)=64 by norm_num]
    ring
  have hm := (square_scaled_unit A (unit_of_mod2_one A ha) 6 y hY).2
  apply (dyadic_unit_rows _ _ hn8 (residue8_unit_cases U hU)).2.1
  simpa only [A,map_mul,map_add,map_sub,map_pow,map_natCast] using hm

private theorem valuation_three_impossible {n : ℕ} (hn2 : (n:ZMod 2)=1)
    {x y : ℚ_[2]} (hx : x ≠ 0) (hv : x.valuation=3) (hy : y^2=x*g n x) : False := by
  obtain ⟨U,hU,hxU⟩ := actual_unit_normal x hx 3 hv
  have hxU' : x=8*(U:ℚ_[2]) := by
    rw [show (8:ℚ_[2])=(2:ℚ_[2])^(3:ℤ) by norm_num]
    exact hxU
  let A : ℤ_[2] := U*(4*U^2-2*n*U+n^2)
  have ha : PadicInt.toZMod A=1 := by
    simp only [A,map_add,map_sub,map_mul,map_pow,map_natCast,map_ofNat,
      actual_unit_residue_two U hU,hn2] <;> decide
  have hY : y^2=(2:ℚ_[2])^(7:ℤ)*(A:ℚ_[2]) := by
    rw [hy,g,hxU']
    dsimp [A]
    push_cast
    rw [show (2:ℚ_[2])^(7:ℤ)=128 by norm_num]
    have hc2 : ((2 : ℤ_[2]) : ℚ_[2]) = 2 := by
      change PadicInt.Coe.ringHom (2 : ℤ_[2]) = (2 : ℚ_[2])
      exact map_ofNat PadicInt.Coe.ringHom 2
    have hc4 : ((4 : ℤ_[2]) : ℚ_[2]) = 4 := by
      change PadicInt.Coe.ringHom (4 : ℤ_[2]) = (4 : ℚ_[2])
      exact map_ofNat PadicInt.Coe.ringHom 4
    simp only [hc2,hc4]
    ring
  have hv' := (square_scaled_unit A (unit_of_mod2_one A ha) 7 y hY).1
  omega

private theorem actual_affine_class {n : ℕ} (hn : 0<n) (hr : (n:ZMod 12)=11)
    {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y^2=x*g n x) :
    classOf x hx=1 ∨ classOf x hx=classOf (5:ℚ_[2]) (by norm_num) := by
  have hres := selected_residues n hr
  have hcases : x.valuation<0 ∨ x.valuation=0 ∨ x.valuation=1 ∨
      x.valuation=2 ∨ x.valuation=3 ∨ x.valuation=4 ∨ 5≤x.valuation := by omega
  rcases hcases with h|h|h|h|h|h|h
  · obtain ⟨u,hu,he⟩ := square_factor_low (n:=n) hx h
    exact Or.inl ((class_of_factor hx one_ne_zero hu hy he).trans class_of_one)
  · obtain ⟨u,hu,he⟩ := five_factor_zero hres.2 hx h
    exact Or.inr (class_of_factor hx (by norm_num) hu hy he)
  · exact (valuation_one_impossible hres.1 hx h hy).elim
  · exact (valuation_two_impossible hres.1 hres.2 hx h hy).elim
  · exact (valuation_three_impossible hres.1 hx h hy).elim
  · obtain ⟨u,hu,he⟩ := five_factor_four hres.2 hx h
    exact Or.inr (class_of_factor hx (by norm_num) hu hy he)
  · obtain ⟨u,hu,he⟩ := square_factor_high hn hres.1 hx h
    exact Or.inl ((class_of_factor hx one_ne_zero hu hy he).trans class_of_one)

/-- All actual target points at Q₂, including infinity and the zero
root. No chord product law, isogeny choice, or corank is used. -/
theorem actual_dyadic_class_upper (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11)
    (P : TargetPoint (n:ℚ_[2])) :
    targetClass P=1 ∨ targetClass P=classOf (5:ℚ_[2]) (by norm_num) := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y H =>
    by_cases hx : x=0
    · exact Or.inl (by simp [targetClass,hx])
    · have he := H.left
      rw [WeierstrassCurve.Affine.equation_iff] at he
      simp only [targetModel,zero_mul,add_zero,zero_add] at he
      have hy : y^2=x*g n x := by dsimp [g]; linear_combination he
      simpa only [targetClass,dif_neg hx] using actual_affine_class hn hr hx hy

theorem local_system_two_size_of_chord (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11)
    (L : LocalSystem n hn) (hm : XClassProduct (n:ℚ_[2])) :
    L.finiteCokernelCard 2 Nat.prime_two=2 :=
  local_system_two_size n hn hr L hm (actual_dyadic_class_upper n hn hr)

end OriginalCasselsDyadicClassUpper318

#print axioms OriginalCasselsDyadicClassUpper318.actual_dyadic_class_upper
#print axioms OriginalCasselsDyadicClassUpper318.local_system_two_size_of_chord
