module
public import ContactPrimeLimits318
public import ScalarSource318
public section
noncomputable section
namespace ScalarContactMap318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain
open ContactRadical318 ContactPrimeLimits318 ConcretePadic318 ScalarSource318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The scalar beta uses the original five-contact homogeneous coordinates,
not the detector Mobius transform. -/
@[expose] def scalarPrimes (w:Assignment) : Finset ℕ :=
  contactPrimes (beta w).num (beta w).den

lemma rational_form_identities (b:ℚ) :
    (forms b.num b.den 2:ℚ)=(b.den:ℚ)*(b-1) ∧
    (forms b.num b.den 3:ℚ)=(b.den:ℚ)*(b-2401) ∧
    (forms b.num b.den 4:ℚ)=(b.den:ℚ)*(32*b+343) := by
  have hh:=b.den_mul_eq_num
  norm_num [forms]
  constructor
  · nlinarith only [hh]
  constructor <;> nlinarith only [hh]

/-- beta=0 is separated explicitly. Every other contact form is forced
nonzero by the actual source scalar polynomial and denominator. -/
theorem source_forms_nonzero (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hb:beta w≠0) : ∀j:Fin 5,forms (beta w).num (beta w).den j≠0 := by
  have hr := (r_inverse S w source).1
  rw [r_formula S w source] at hr
  have hf : beta w-1≠0 ∧ beta w-2401≠0 ∧ 32*beta w+343≠0 ∧ 2*beta w-1≠0 := by
    simpa only [mul_ne_zero_iff,and_assoc] using hr
  have hd : ((beta w).den:ℚ)≠0 := by exact_mod_cast (beta w).den_nz
  have hnum : (beta w).num≠0 := by
    intro hz
    have hh := (beta w).den_mul_eq_num
    rw [hz,Int.cast_zero] at hh
    exact hb ((mul_eq_zero.mp hh).resolve_left hd)
  intro j
  fin_cases j <;> dsimp only at *
  · simpa [forms] using (show ((beta w).den:ℤ)≠0 by exact_mod_cast (beta w).den_nz)
  · simpa [forms] using hnum
  · intro hz
    norm_num [forms] at hz
    have hq : ((beta w).num:ℚ)-(beta w).den=0 := by exact_mod_cast hz
    apply mul_ne_zero hd hf.1
    nlinarith only [(beta w).den_mul_eq_num,hq]
  · intro hz
    norm_num [forms] at hz
    have hq : ((beta w).num:ℚ)-2401*(beta w).den=0 := by exact_mod_cast hz
    apply mul_ne_zero hd hf.2.1
    nlinarith only [(beta w).den_mul_eq_num,hq]
  · intro hz
    norm_num [forms] at hz
    have hq : 32*((beta w).num:ℚ)+343*(beta w).den=0 := by exact_mod_cast hz
    apply mul_ne_zero hd hf.2.2.1
    nlinarith only [(beta w).den_mul_eq_num,hq]

variable (p:ℕ) [Fact p.Prime]

lemma coefficient3723_unit (hg:p∉badPrimes) : padicValRat p (3723:ℚ)=0 := by
  have h3 := good_not_dvd p 3 Fact.out hg (by simp [badPrimes])
  have h17 := good_not_dvd p 17 Fact.out hg (by simp [badPrimes])
  have h73 := good_not_dvd p 73 Fact.out hg (by simp [badPrimes])
  have hn : ¬p∣(3723:ℕ) := by
    have he : (3723:ℕ)=3*17*73 := by norm_num
    simpa only [he,(Fact.out:p.Prime).dvd_mul,h3,h17,h73,or_self,not_false_eq_true]
  change padicValRat p ((3723:ℤ):ℚ)=0
  rw [padicValRat.of_int,padicValInt.eq_zero_of_not_dvd (by simpa [Int.natCast_dvd] using hn)]
  norm_num

lemma beta_value_even (w:Assignment) (hb:beta w≠0) (hg:p∉badPrimes) :
    Even (padicValRat p (beta w)) := by
  have hs : 2*w 0+1≠0 := by
    intro hs
    apply hb
    simp only [beta,hs,zero_pow (by decide : 2≠0),mul_zero]
  rw [beta,padicValRat.mul (by norm_num) (pow_ne_zero _ hs),
    coefficient3723_unit p hg,padicValRat.pow,zero_add]
  exact ⟨padicValRat p (2*w 0+1),by ring⟩

/-- Good odd-contact primes cannot come from beta's zero or infinity forms.
This uses actual reduced numerator/denominator parity, not a valuation model. -/
lemma beta_num_den_even (w:Assignment) (hb:beta w≠0) (hg:p∉badPrimes) :
    Even (padicValInt p (beta w).num) ∧ Even (padicValInt p ((beta w).den:ℤ)) := by
  have hh := Rat.num_den_even_padicVal_of_even_padicVal Fact.out (beta_value_even p w hb hg)
  simpa only [padicValInt,Int.natAbs_natCast] using hh

lemma member_nonzero_noninfinite (w:Assignment) (hb:beta w≠0) (hp:p∈scalarPrimes w) :
    ∃j:Fin 5,j≠0 ∧ j≠1 ∧ p∈(forms (beta w).num (beta w).den j).natAbs.primeFactors ∧
      p∉badPrimes ∧ Odd (padicValInt p (forms (beta w).num (beta w).den j)) := by
  obtain ⟨j,hj,hg,ho⟩ := (mem_contactPrimes _ _ p).mp hp
  obtain ⟨hn,hd⟩ := beta_num_den_even p w hb hg
  refine ⟨j,?_,?_,hj,hg,ho⟩
  · intro he
    rw [he] at ho
    simp only [forms,Matrix.cons_val_zero] at ho
    exact (Nat.not_even_iff_odd.mpr ho) hd
  · intro he
    rw [he] at ho
    simp only [forms,Matrix.cons_val_one,Matrix.cons_val_zero] at ho
    exact (Nat.not_even_iff_odd.mpr ho) hn

#print axioms rational_form_identities
#print axioms source_forms_nonzero
#print axioms coefficient3723_unit
#print axioms beta_value_even
#print axioms beta_num_den_even
#print axioms member_nonzero_noninfinite
end ScalarContactMap318
