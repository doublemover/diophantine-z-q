module
public import CTActualPrimeScalarRows318
import all CTExplicitLocalBitForms318
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section
noncomputable section

namespace CTActualSignedGeneratorsQR318

open CTActualPrimeScalarRows318 CTActualRetainedScalarPair318 CTActualFiniteIsogenyLinear318
open CTNativeOddSquareclassCoordinates318 CTNativeDyadicSquareclassCoordinates318
open CTExplicitLocalBitForms318 CTPrimeReciprocityBitCancellation318
open ActualNaturalAllPlacesFinite318
open scoped BigOperators

local instance {n : ℕ} (i : Support n) : Fact i.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors i.property⟩

def twoIndex (n : ℕ) (hn : 0<n) : Support n :=
  ⟨2,Nat.mem_primeFactors.mpr ⟨Nat.prime_two,dvd_mul_of_dvd_left (by decide : 2∣6) n,
    mul_ne_zero (by decide) hn.ne'⟩⟩

private theorem idx_val_eq {n : ℕ} (i j : Support n) : i.val=j.val ↔ i=j :=
  ⟨Subtype.ext,congrArg Subtype.val⟩

private theorem idx_val_two {n : ℕ} (hn : 0<n) (i : Support n) :
    i.val=2 ↔ i=twoIndex n hn := idx_val_eq i (twoIndex n hn)

def minusOneTuple (n : ℕ) : RetainedSpace n :=
  (negOneLabel ℝ,fun i => negOneLabel ℚ_[i.val])

def primeTuple (n : ℕ) (q : Support n) : RetainedSpace n :=
  (primeLabel ℝ q.val (Fact.out : q.val.Prime).ne_zero,
    fun i => primeLabel ℚ_[i.val] q.val (Fact.out : q.val.Prime).ne_zero)

abbrev DRow := F₂ × F₂ × F₂
abbrev ORow := F₂ × F₂

def dyadicNaturalRow (q : ℕ) : DRow :=
  if q=2 then (1,0,0) else (0,epsilonBit (q:ZMod 8),omegaBit (q:ZMod 8))

def oddNaturalRow (p : ℕ) [Fact p.Prime] (q : ℕ) : ORow :=
  if p=q then (1,0) else (0,signBit (legendreSym p q))

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem dyadic_natural_row (q : ℕ) [Fact q.Prime] :
    dyadicVector (primeLabel ℚ_[2] q (Fact.out : q.Prime).ne_zero)=dyadicNaturalRow q := by
  by_cases hq : q=2
  · subst q
    rw [dyadicNaturalRow,if_pos rfl]
    exact actual_dyadic_two
  · rw [dyadicNaturalRow,if_neg hq]
    exact actual_dyadic_odd_natural q (Fact.out : q.Prime).ne_zero (odd_prime_mod_two hq)

private theorem odd_natural_row (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    oddVector p (primeLabel ℚ_[p] q (Fact.out : q.Prime).ne_zero)=oddNaturalRow p q := by
  by_cases h : p=q
  · subst q
    rw [oddNaturalRow,if_pos rfl]
    exact actual_odd_own p
  · rw [oddNaturalRow,if_neg h]
    have hD : ¬p∣q := by
      intro hd
      rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hd with h1|h2
      · exact (Fact.out : p.Prime).ne_one h1
      · exact h h2
    exact actual_odd_natural_unit p q (Fact.out : q.Prime).ne_zero hD

private theorem padic_zeros_row (p : ℕ) [Fact p.Prime] :
    localPrimeForm p (negOneLabel ℚ_[p]) (negOneLabel ℚ_[p])=
      if p=2 then (1:F₂) else 0 := by
  by_cases h2 : p=2
  · subst p
    rw [localPrimeForm_two,dyadicForm_apply,actual_dyadic_minus_one,if_pos rfl] <;> decide
  · rw [localPrimeForm_odd p h2,oddForm_apply,actual_odd_minus_one,if_neg h2]
    simp [odd]

private theorem padic_mixed_row (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    localPrimeForm p (negOneLabel ℚ_[p]) (primeLabel ℚ_[p] q (Fact.out : q.Prime).ne_zero)=
      (if p=2 then dyadic (0,1,0) (dyadicNaturalRow q) else 0)+
      (if p=q then (if q=2 then 0 else oddSign q) else 0) := by
  by_cases h2 : p=2
  · subst p
    rw [localPrimeForm_two,dyadicForm_apply,actual_dyadic_minus_one,dyadic_natural_row,if_pos rfl]
    by_cases hq : q=2
    · subst q
      simp
    · simp [Ne.symm hq]
  · rw [if_neg h2,zero_add,localPrimeForm_odd p h2,oddForm_apply,actual_odd_minus_one,odd_natural_row]
    by_cases hq : p=q
    · subst q
      simp [oddNaturalRow,odd,h2]
    · simp [oddNaturalRow,odd,hq]

private theorem padic_self_row (p q : ℕ) [Fact p.Prime] [Fact q.Prime] :
    localPrimeForm p (primeLabel ℚ_[p] q (Fact.out : q.Prime).ne_zero)
      (primeLabel ℚ_[p] q (Fact.out : q.Prime).ne_zero)=
      (if p=2 then dyadic (dyadicNaturalRow q) (dyadicNaturalRow q) else 0)+
      (if p=q then (if q=2 then 0 else oddSign q) else 0) := by
  by_cases h2 : p=2
  · subst p
    rw [localPrimeForm_two,dyadicForm_apply,dyadic_natural_row,if_pos rfl]
    by_cases hq : q=2
    · subst q
      simp
    · simp [Ne.symm hq]
  · rw [if_neg h2,zero_add,localPrimeForm_odd p h2,oddForm_apply,odd_natural_row]
    by_cases hq : p=q
    · subst q
      simp [oddNaturalRow,odd,h2]
    · simp [oddNaturalRow,odd,hq]

private theorem padic_distinct_row (p q r : ℕ) [Fact p.Prime] [Fact q.Prime] [Fact r.Prime]
    (hqr : q≠r) :
    localPrimeForm p (primeLabel ℚ_[p] q (Fact.out : q.Prime).ne_zero)
      (primeLabel ℚ_[p] r (Fact.out : r.Prime).ne_zero)=
      (if p=2 then dyadic (dyadicNaturalRow q) (dyadicNaturalRow r) else 0)+
      (if p=q then (if q=2 then 0 else signBit (legendreSym q r)) else 0)+
      (if p=r then (if r=2 then 0 else signBit (legendreSym r q)) else 0) := by
  by_cases h2 : p=2
  · subst p
    simp only [localPrimeForm_two,dyadicForm_apply,dyadic_natural_row,if_pos rfl]
    by_cases hq : q=2 <;> by_cases hr : r=2
    · exact False.elim (hqr (hq.trans hr.symm))
    · subst q
      simp [Ne.symm hr]
    · subst r
      simp [Ne.symm hq]
    · simp [Ne.symm hq,Ne.symm hr]
  · simp only [if_neg h2,zero_add,localPrimeForm_odd p h2,oddForm_apply,odd_natural_row]
    by_cases hq : p=q
    · subst q
      simp [oddNaturalRow,odd,h2,hqr]
    · by_cases hr : p=r
      · subst r
        simp [oddNaturalRow,odd,h2,hq]
      · simp [oddNaturalRow,odd,hq,hr]

private theorem dyadic_add_self (u : F₂) : u+u=0 := (by decide : ∀ t : F₂, t+t=0) u
private theorem dyadic_idem (u : F₂) : u*u=u := (by decide : ∀ t : F₂, t*t=t) u

/-- Uses the true −1 class at every completion. The real and dyadic
coordinates each contribute 1 and the other retained primes contribute 0. -/
theorem qr_minus_one_self (n : ℕ) (hn : 0<n) :
    retainedForm n (minusOneTuple n) (minusOneTuple n)=0 := by
  rw [retainedForm_apply]
  change realForm (negOneLabel ℝ) (negOneLabel ℝ)+
    (∑ i : Support n,localPrimeForm i.val (negOneLabel ℚ_[i.val]) (negOneLabel ℚ_[i.val]))=0
  simp only [realForm_apply,actual_real_minus_one,mul_one,padic_zeros_row,idx_val_two hn]
  have hSum : (∑ i : Support n, if i=twoIndex n hn then (1:F₂) else 0)=1 := by simp
  rw [hSum] <;> decide

theorem qr_minus_one_prime (n : ℕ) (hn : 0<n) (q : Support n) :
    retainedForm n (minusOneTuple n) (primeTuple n q)=0 := by
  rw [retainedForm_apply]
  change realForm (negOneLabel ℝ) (primeLabel ℝ q.val (Fact.out : q.val.Prime).ne_zero)+
    (∑ i : Support n,localPrimeForm i.val (negOneLabel ℚ_[i.val])
      (primeLabel ℚ_[i.val] q.val (Fact.out : q.val.Prime).ne_zero))=0
  simp only [realForm_apply,actual_real_natural,mul_zero,zero_add,padic_mixed_row,
    idx_val_two hn,idx_val_eq,Finset.sum_add_distrib]
  have hSum (i : Support n) (a : F₂) : (∑ j : Support n, if j=i then a else 0)=a := by simp
  simp only [hSum]
  by_cases hq : q.val=2
  · rw [if_pos ((idx_val_two hn q).mp hq),dyadicNaturalRow,if_pos hq] <;> decide
  · rw [if_neg ((idx_val_two hn q).not.mpr hq),dyadicNaturalRow,if_neg hq]
    rw [oddSign,minusOne_bit_row hq]
    simp [dyadic,dyadic_add_self]

theorem qr_prime_self (n : ℕ) (hn : 0<n) (q : Support n) :
    retainedForm n (primeTuple n q) (primeTuple n q)=0 := by
  rw [retainedForm_apply]
  change realForm (primeLabel ℝ q.val (Fact.out : q.val.Prime).ne_zero) _+
    (∑ i : Support n,localPrimeForm i.val (primeLabel ℚ_[i.val] q.val (Fact.out : q.val.Prime).ne_zero)
      (primeLabel ℚ_[i.val] q.val (Fact.out : q.val.Prime).ne_zero))=0
  simp only [realForm_apply,actual_real_natural,mul_zero,zero_add,padic_self_row,
    idx_val_two hn,idx_val_eq,Finset.sum_add_distrib]
  have hSum (i : Support n) (a : F₂) : (∑ j : Support n, if j=i then a else 0)=a := by simp
  simp only [hSum]
  by_cases hq : q.val=2
  · rw [if_pos ((idx_val_two hn q).mp hq),dyadicNaturalRow,if_pos hq] <;> decide
  · rw [if_neg ((idx_val_two hn q).not.mpr hq),dyadicNaturalRow,if_neg hq]
    rw [oddSign,minusOne_bit_row hq]
    simp [dyadic,dyadic_idem,dyadic_add_self]

theorem qr_primes_distinct (n : ℕ) (hn : 0<n) (q r : Support n) (hqr : q≠r) :
    retainedForm n (primeTuple n q) (primeTuple n r)=0 := by
  have hqr' : q.val≠r.val := (idx_val_eq q r).not.mpr hqr
  rw [retainedForm_apply]
  change realForm (primeLabel ℝ q.val (Fact.out : q.val.Prime).ne_zero)
    (primeLabel ℝ r.val (Fact.out : r.val.Prime).ne_zero)+
    (∑ i : Support n,localPrimeForm i.val (primeLabel ℚ_[i.val] q.val (Fact.out : q.val.Prime).ne_zero)
      (primeLabel ℚ_[i.val] r.val (Fact.out : r.val.Prime).ne_zero))=0
  simp only [realForm_apply,actual_real_natural,mul_zero,zero_add,padic_distinct_row _ _ _ hqr',
    idx_val_two hn,idx_val_eq,Finset.sum_add_distrib]
  have hSum (i : Support n) (a : F₂) : (∑ j : Support n, if j=i then a else 0)=a := by simp
  simp only [hSum]
  by_cases hq : q.val=2 <;> by_cases hr : r.val=2
  · exact False.elim (hqr' (hq.trans hr.symm))
  · rw [if_pos ((idx_val_two hn q).mp hq),if_neg ((idx_val_two hn r).not.mpr hr)]
    rw [hq,two_bit_row hr]
    simp [dyadicNaturalRow,hr,dyadic,dyadic_add_self]
  · rw [if_neg ((idx_val_two hn q).not.mpr hq),if_pos ((idx_val_two hn r).mp hr)]
    rw [hr,two_bit_row hq]
    simp [dyadicNaturalRow,hq,dyadic,dyadic_add_self]
  · rw [if_neg ((idx_val_two hn q).not.mpr hq),if_neg ((idx_val_two hn r).not.mpr hr)]
    simpa [dyadicNaturalRow,hq,hr,dyadic] using distinct_odd_bit_sum hq hr hqr'

end CTActualSignedGeneratorsQR318

#print axioms CTActualSignedGeneratorsQR318.qr_minus_one_self
#print axioms CTActualSignedGeneratorsQR318.qr_minus_one_prime
#print axioms CTActualSignedGeneratorsQR318.qr_prime_self
#print axioms CTActualSignedGeneratorsQR318.qr_primes_distinct
