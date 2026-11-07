module
public import ContactPrimeLimits318
public section
namespace DetectorContactMap318
open ContactRadical318 ContactPrimeLimits318 FiniteContact318 ConcretePadic318 RawWeights318
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def coefficient : Fin 5→ℤ := ![1,2,1,-2399,407]
@[expose] def offset : Fin 5→ℤ := ![0,1,1,1,32]

 theorem form_linear (t:ℚ) (j:Fin 5) :
    forms (2*t.num+t.den) t.num j=coefficient j*t.num+offset j*t.den := by
  fin_cases j <;> norm_num [forms,coefficient,offset] <;> ring

 theorem coefficient_nonzero (j:Fin 5) : coefficient j≠0 := by
  fin_cases j <;> norm_num [coefficient]

 theorem coefficient_support (j:Fin 5) : (coefficient j).natAbs∣contactModulus^8 := by
  fin_cases j <;> norm_num [coefficient,contactModulus]

/-- Exact binding of each primitive contact form to the rational source factor. -/
 theorem form_identity (t:ℚ) (j:Fin 5) :
    (forms (2*t.num+t.den) t.num j:ℚ)=(coefficient j:ℚ)*(t.den:ℚ)*(t-root j) := by
  have hh:=t.den_mul_eq_num
  fin_cases j <;> norm_num [forms,coefficient,root,point] <;>
    nlinarith only [hh]

 theorem forms_nonzero_of_contactPolynomial (t:ℚ) (hF:contactPolynomial t≠0) :
    ∀j:Fin 5,forms (2*t.num+t.den) t.num j≠0 := by
  intro j
  have hp : ∀j:Fin 5,t-root j≠0 := by
    rw [polynomial_product] at hF
    exact fun j=>(Finset.prod_ne_zero_iff.mp hF) j (Finset.mem_univ j)
  have hh : (forms (2*t.num+t.den) t.num j:ℚ)≠0 := by
    rw [form_identity]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast coefficient_nonzero j)
      (by exact_mod_cast t.den_nz)) (hp j)
  exact fun he=>hh (by rw [he]; norm_num)

variable (p:ℕ) [Fact p.Prime]

 theorem coefficient_not_dvd (hg:p∉badPrimes) (j:Fin 5) : ¬(p:ℤ)∣coefficient j := by
  rw [Int.natCast_dvd]
  exact not_dvd_supported p (good_exclusions p Fact.out hg).2.1 _ (coefficient_support j)

 theorem denominator_not_dvd (t:ℚ) (j:Fin 5) (hg:p∉badPrimes)
    (hd:p∈(forms (2*t.num+t.den) t.num j).natAbs.primeFactors) : ¬(p:ℤ)∣(t.den:ℤ) := by
  intro hb
  have hform:(p:ℤ)∣forms (2*t.num+t.den) t.num j :=
    Int.natCast_dvd.mpr (Nat.mem_primeFactors.mp hd).2.1
  have hprod:(p:ℤ)∣coefficient j*t.num := by
    rw [form_linear] at hform
    have hd:=dvd_sub hform (dvd_mul_of_dvd_right hb (offset j))
    simpa only [add_sub_cancel_right] using hd
  have hpZ:Prime (p:ℤ):=Nat.prime_iff_prime_int.mp Fact.out
  have ha:(p:ℤ)∣t.num := (hpZ.dvd_mul.mp hprod).resolve_left (coefficient_not_dvd p hg j)
  exact hpZ.not_unit ((Rat.isCoprime_num_den t).isUnit_of_dvd' ha hb)

 theorem coefficient_unit (hg:p∉badPrimes) (j:Fin 5) : rationalPlace p (coefficient j:ℚ)=0 := by
  rw [rational_value p _ (by exact_mod_cast coefficient_nonzero j),padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd (coefficient_not_dvd p hg j)]
  norm_num

 theorem member_raw_contact (t:ℚ) (hp:p∈detectorPrimes t) :
    ∃j:Fin 5,∃f:ℤ, rationalPlace p (t-root j)=f ∧ 0<f ∧ Odd f := by
  obtain ⟨j,hj,hg,ho⟩:=(mem_contactPrimes _ _ p).mp hp
  have hfne : forms (2*t.num+t.den) t.num j≠0 := by
    have hh: (forms (2*t.num+t.den) t.num j).natAbs≠0 := (Nat.mem_primeFactors.mp hj).2.2
    simpa only [Int.natAbs_ne_zero] using hh
  have hb:=denominator_not_dvd p t j hg hj
  have hbval:rationalPlace p (t.den:ℚ)=0 := by
    rw [rational_value p _ (by exact_mod_cast t.den_nz)]
    change ((padicValRat p ((t.den:ℤ):ℚ):ℤ):WithTop ℤ)=0
    rw [padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hb]
    norm_num
  have hfv:rationalPlace p (forms (2*t.num+t.den) t.num j:ℚ)=
      ((padicValInt p (forms (2*t.num+t.den) t.num j):ℤ):WithTop ℤ) := by
    rw [rational_value p _ (by exact_mod_cast hfne),padicValRat.of_int]
  rw [form_identity,(rationalPlace p).map_mul,(rationalPlace p).map_mul,
    coefficient_unit p hg j,hbval,zero_add,zero_add] at hfv
  refine ⟨j,_,hfv,?_,?_⟩
  · have hh:padicValInt p (forms (2*t.num+t.den) t.num j)≠0 := by
      intro hz
      rw [hz] at ho
      norm_num at ho
    exact_mod_cast Nat.pos_of_ne_zero hh
  · exact_mod_cast ho

end
end DetectorContactMap318
#print axioms DetectorContactMap318.forms_nonzero_of_contactPolynomial
#print axioms DetectorContactMap318.member_raw_contact
