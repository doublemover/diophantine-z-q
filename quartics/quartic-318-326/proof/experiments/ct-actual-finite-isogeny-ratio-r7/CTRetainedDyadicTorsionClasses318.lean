module
public import OriginalCasselsDyadicNormalize318
public import ActualTwoDescentSquareClassQuotient318
import Mathlib.Tactic.NormNum
import Mathlib.Data.Fintype.Prod
import Lean.Elab.Tactic.Omega
public section

noncomputable section

namespace CTRetainedDyadicTorsionClasses318

open OriginalCasselsDyadicNormalize318 ActualTwoDescentTwoAdicUnits318
open ActualTwoDescentSquareClassQuotient318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Equality of actual dyadic unit squareclasses is exact equality of
their residues under the same integral ring reduction. -/
theorem unit_class_iff_res8 (A B : ℤ_[2]) (hA : IsUnit A) (hB : IsUnit B) :
    classOf (A:ℚ_[2]) (PadicInt.coe_ne_zero.mpr hA.ne_zero) =
      classOf (B:ℚ_[2]) (PadicInt.coe_ne_zero.mpr hB.ne_zero) ↔ res8 A = res8 B := by
  have hA0 : (A:ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr hA.ne_zero
  have hB0 : (B:ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr hB.ne_zero
  rw [class_of_eq_iff _ _ hA0 hB0]
  constructor
  · rintro ⟨s,hs,hEq⟩
    have hv := congrArg Padic.valuation hEq
    rw [val_of_unit A hA,Padic.valuation_mul hB0 (pow_ne_zero _ hs),
      val_of_unit B hB,Padic.valuation_pow,zero_add] at hv
    have hs0 : s.valuation=0 := by omega
    obtain ⟨S,hS,hSU⟩ := actual_two_unit_lift s hs hs0
    have hIntegral : A=B*S^2 := by
      apply PadicInt.ext
      simpa only [PadicInt.coe_mul,PadicInt.coe_pow,hS] using hEq
    have he := congrArg res8 hIntegral
    rw [map_mul,map_pow,actual_unit_square_mod8 _ (hSU.map res8),mul_one] at he
    exact he
  · intro hEq
    let u : ℤ_[2]ˣ := hB.unit
    have hu : (u:ℤ_[2])=B := hB.unit_spec
    let C : ℤ_[2] := A*(↑u⁻¹ : ℤ_[2])
    have hm : C*B=A := calc
      C*B = A*((↑u⁻¹ : ℤ_[2])*(u:ℤ_[2])) := by rw [hu]; exact mul_assoc _ _ _
      _ = A := by rw [← Units.val_mul,inv_mul_cancel,Units.val_one,mul_one]
    have hCr : res8 C=1 := by
      apply (hB.map res8).mul_right_cancel
      rw [← map_mul,hm,hEq,one_mul]
    obtain ⟨s,hs,hS⟩ := square_of_res8_one C hCr
    refine ⟨s,hs,?_⟩
    have he := congrArg (fun z : ℤ_[2] => (z:ℚ_[2])) hm
    rw [PadicInt.coe_mul,←hS] at he
    exact he.symm.trans (mul_comm _ _)

/-- The four labels are literally (1,-3,n,-3n), in this order.
The -3 label is the squareclass of B=-3n² at the source kernel. -/
@[expose] def torsionUnit (n : ℕ) (i : Bool × Bool) : ℤ_[2] :=
  if i.1 then (if i.2 then (-3)*(n:ℤ_[2]) else n)
  else (if i.2 then -3 else 1)

private def residueLabel (r : ZMod 8) (i : Bool × Bool) : ZMod 8 :=
  if i.1 then (if i.2 then (-3)*r else r) else (if i.2 then -3 else 1)

private theorem torsionUnit_isUnit (n : ℕ) (h : (n:ZMod 2)=1) (i : Bool × Bool) :
    IsUnit (torsionUnit n i) := by
  apply unit_of_mod2_one
  rcases i with ⟨a,b⟩
  cases a <;> cases b <;> simp [torsionUnit,h,map_ofNat, show (-(3:ZMod 2))=1 by decide]

private theorem torsionUnit_res8 (n : ℕ) (i : Bool × Bool) :
    res8 (torsionUnit n i)=residueLabel (n:ZMod 8) i := by
  rcases i with ⟨a,b⟩
  cases a <;> cases b <;> simp [torsionUnit,residueLabel,map_ofNat]

private theorem table_three :
    (∀ i j : Bool × Bool, residueLabel 3 i=residueLabel 3 j → i=j) ∧
    (∀ r : Fin 8, Nat.Coprime r.val 8 →
      ∃ i : Bool × Bool, residueLabel 3 i = (r.val:ZMod 8)) := by decide

private theorem table_seven :
    (∀ i j : Bool × Bool, residueLabel 7 i=residueLabel 7 j → i=j) ∧
    (∀ r : Fin 8, Nat.Coprime r.val 8 →
      ∃ i : Bool × Bool, residueLabel 7 i = (r.val:ZMod 8)) := by decide

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

def torsionClass (n : ℕ) (hr : (n:ZMod 12)=11) (i : Bool × Bool) : SquareClass ℚ_[2] :=
  classOf ((torsionUnit n i:ℤ_[2]):ℚ_[2])
    (PadicInt.coe_ne_zero.mpr (torsionUnit_isUnit n (selected_residues n hr).1 i).ne_zero)

theorem torsionClass_injective (n : ℕ) (hr : (n:ZMod 12)=11) :
    Function.Injective (torsionClass n hr) := by
  intro i j h
  obtain ⟨h2,h8⟩ := selected_residues n hr
  have hx := (unit_class_iff_res8 (torsionUnit n i) (torsionUnit n j)
    (torsionUnit_isUnit n h2 i) (torsionUnit_isUnit n h2 j)).mp h
  simp only [torsionUnit_res8] at hx
  rcases h8 with h8 | h8
  · rw [h8] at hx
    exact table_three.1 i j hx
  · rw [h8] at hx
    exact table_seven.1 i j hx

theorem unit_class_is_torsion (n : ℕ) (hr : (n:ZMod 12)=11)
    (A : ℤ_[2]) (hA : IsUnit A) :
    ∃ i : Bool × Bool, classOf (A:ℚ_[2]) (PadicInt.coe_ne_zero.mpr hA.ne_zero) =
      torsionClass n hr i := by
  obtain ⟨h2,h8⟩ := selected_residues n hr
  have hc : Nat.Coprime (res8 A).val 8 :=
    (ZMod.isUnit_iff_coprime _ 8).mp
      (by simpa only [ZMod.natCast_zmod_val] using hA.map res8)
  let r : Fin 8 := ⟨(res8 A).val,ZMod.val_lt (res8 A)⟩
  have hFind : ∃ i : Bool × Bool, residueLabel (n:ZMod 8) i=res8 A := by
    rcases h8 with h | h
    · rw [h]
      simpa only [r,ZMod.natCast_zmod_val] using table_three.2 r hc
    · rw [h]
      simpa only [r,ZMod.natCast_zmod_val] using table_seven.2 r hc
  obtain ⟨i,hi⟩ := hFind
  refine ⟨i,(unit_class_iff_res8 A (torsionUnit n i) hA (torsionUnit_isUnit n h2 i)).mpr ?_⟩
  rw [torsionUnit_res8,hi]

/-- The labels classify every actual field squareclass of even valuation,
including negative even valuations, not just integral point labels. -/
theorem even_valuation_class_is_torsion (n : ℕ) (hr : (n:ZMod 12)=11)
    (a : ℚ_[2]) (ha : a≠0) (hv : a.valuation%2=0) :
    ∃ i : Bool × Bool, classOf a ha = torsionClass n hr i := by
  obtain ⟨A,hA,he⟩ := actual_unit_normal a ha a.valuation rfl
  let k := a.valuation/2
  have hk : a.valuation=k+k := by dsimp [k]; omega
  have h₂ : (2:ℚ_[2]) ≠ 0 := by norm_num
  have hA0 : (A:ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.mpr hA.ne_zero
  have hEq : classOf a ha = classOf (A:ℚ_[2]) hA0 := by
    apply (class_of_eq_iff _ _ _ _).mpr
    refine ⟨(2:ℚ_[2])^k,zpow_ne_zero k h₂,?_⟩
    calc
      a = (2:ℚ_[2])^(k+k)*(A:ℚ_[2]) := by rw [←hk]; exact he
      _ = (A:ℚ_[2])*((2:ℚ_[2])^k)^2 := by
        rw [zpow_add₀ h₂,pow_two]
        ac_rfl
  obtain ⟨i,hi⟩ := unit_class_is_torsion n hr A hA
  exact ⟨i,hEq.trans hi⟩

theorem torsionClass_zero (n : ℕ) (hr : (n:ZMod 12)=11) :
    torsionClass n hr (false,false)=1 := by
  unfold torsionClass torsionUnit
  have h := class_of_one (K:=ℚ_[2])
  change classOf (PadicInt.Coe.ringHom (1:ℤ_[2])) _=1
  rw [map_one] <;> exact h

theorem torsionClass_kernel (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    torsionClass n hr (false,true)=
      classOf (-3*(n:ℚ_[2])^2) (mul_ne_zero (by norm_num) (pow_ne_zero _ (Nat.cast_ne_zero.mpr hn.ne'))) := by
  unfold torsionClass torsionUnit
  symm
  apply (class_of_eq_iff _ _ _ _).mpr
  refine ⟨n,Nat.cast_ne_zero.mpr hn.ne',?_⟩
  change -3*(n:ℚ_[2])^2 = PadicInt.Coe.ringHom (-(3:ℤ_[2]))*(n:ℚ_[2])^2
  rw [map_neg,map_ofNat]

theorem torsionClass_first (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    torsionClass n hr (true,false)=classOf (n:ℚ_[2]) (Nat.cast_ne_zero.mpr hn.ne') := by
  unfold torsionClass torsionUnit
  apply (class_of_eq_iff _ _ _ _).mpr
  refine ⟨1,one_ne_zero,?_⟩
  change PadicInt.Coe.ringHom (n:ℤ_[2])=(n:ℚ_[2])*1^2
  rw [map_natCast,one_pow,mul_one]

theorem torsionClass_last (n : ℕ) (hn : 0<n) (hr : (n:ZMod 12)=11) :
    torsionClass n hr (true,true)=
      classOf (-3*(n:ℚ_[2])) (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hn.ne')) := by
  unfold torsionClass torsionUnit
  apply (class_of_eq_iff _ _ _ _).mpr
  refine ⟨1,one_ne_zero,?_⟩
  change PadicInt.Coe.ringHom (-3*(n:ℤ_[2]))= -3*(n:ℚ_[2])*1^2
  rw [map_mul,map_neg,map_ofNat,map_natCast,one_pow,mul_one]

end CTRetainedDyadicTorsionClasses318

#print axioms CTRetainedDyadicTorsionClasses318.torsionClass_injective
#print axioms CTRetainedDyadicTorsionClasses318.even_valuation_class_is_torsion
