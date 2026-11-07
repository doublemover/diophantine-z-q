module
public import ScalarContactMap318
public section
noncomputable section
namespace ScalarContactValuation318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain
open ContactRadical318 ContactPrimeLimits318 ConcretePadic318 ScalarSource318 ScalarContactMap318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def modulus : ℕ := 2*3*5*7*359*4801
@[expose] def root : Fin 4→ℚ := ![1,2401,-343/32,1/2]
@[expose] def polynomial (b:ℚ) : ℚ := (b-1)*(b-2401)*(32*b+343)*(2*b-1)
@[expose] def shift (j:Fin 3) : Fin 5 := ⟨j.val+2,by omega⟩
@[expose] def coefficient : Fin 3→ℤ := ![1,1,32]
@[expose] def offset : Fin 3→ℤ := ![-1,-2401,343]

lemma difference_support (i j:Fin 4) (hij:i≠j) :
    root i-root j≠0 ∧ (root i-root j).num.natAbs∣modulus^8 ∧
      (root i-root j).den∣modulus^8 := by
  fin_cases i <;> fin_cases j <;> norm_num [root,modulus] at *

lemma polynomial_product (b:ℚ) : polynomial b=64*∏j:Fin 4,(b-root j) := by
  norm_num [polynomial,root,Fin.prod_univ_four]
  ring

lemma form_linear (b:ℚ) (j:Fin 3) :
    forms b.num b.den (shift j)=coefficient j*b.num+offset j*b.den := by
  fin_cases j <;> norm_num [forms,shift,coefficient,offset] <;> ring

lemma form_identity (b:ℚ) (j:Fin 3) :
    (forms b.num b.den (shift j):ℚ)=(coefficient j:ℚ)*(b.den:ℚ)*(b-root j.castSucc) := by
  have hh := b.den_mul_eq_num
  fin_cases j <;> norm_num [forms,shift,coefficient,root] <;> nlinarith only [hh]

lemma coefficient_nonzero (j:Fin 3) : coefficient j≠0 := by
  fin_cases j <;> norm_num [coefficient]

variable (p:ℕ) [Fact p.Prime]

lemma good_modulus (hg:p∉badPrimes) : ¬p∣modulus := by
  have h2:=good_not_dvd p 2 Fact.out hg (by simp [badPrimes])
  have h3:=good_not_dvd p 3 Fact.out hg (by simp [badPrimes])
  have h5:=good_not_dvd p 5 Fact.out hg (by simp [badPrimes])
  have h7:=good_not_dvd p 7 Fact.out hg (by simp [badPrimes])
  have h359:=good_not_dvd p 359 Fact.out hg (by simp [badPrimes])
  have h4801:=good_not_dvd p 4801 Fact.out hg (by simp [badPrimes])
  simp only [modulus,(Fact.out:p.Prime).dvd_mul,h2,h3,h5,h7,h359,h4801,or_self,not_false_eq_true]

lemma not_dvd_supported (hg:p∉badPrimes) (n:ℕ) (hn:n∣modulus^8) : ¬p∣n := by
  intro hd
  exact good_modulus p hg ((Fact.out:p.Prime).dvd_of_dvd_pow (dvd_trans hd hn))

lemma supported_unit (q:ℚ) (hq:q≠0) (hg:p∉badPrimes)
    (hn:q.num.natAbs∣modulus^8) (hd:q.den∣modulus^8) : rationalPlace p q=0 := by
  rw [rational_value p q hq]
  have hn0 := padicValNat.eq_zero_of_not_dvd (not_dvd_supported p hg _ hn)
  have hd0 := padicValNat.eq_zero_of_not_dvd (not_dvd_supported p hg _ hd)
  simp only [padicValRat,padicValInt,hn0,hd0,Int.natCast_zero,sub_self,WithTop.coe_zero]

lemma difference_unit (hg:p∉badPrimes) (i j:Fin 4) (hij:i≠j) :
    rationalPlace p (root i-root j)=0 := by
  obtain ⟨hz,hn,hd⟩ := difference_support i j hij
  exact supported_unit p _ hz hg hn hd

lemma coefficient_not_dvd (hg:p∉badPrimes) (j:Fin 3) : ¬(p:ℤ)∣coefficient j := by
  rw [Int.natCast_dvd]
  apply not_dvd_supported p hg
  fin_cases j <;> norm_num [coefficient,modulus]

lemma coefficient_unit (hg:p∉badPrimes) (j:Fin 3) : rationalPlace p (coefficient j:ℚ)=0 := by
  rw [rational_value p _ (by exact_mod_cast coefficient_nonzero j),padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd (coefficient_not_dvd p hg j)]
  norm_num

lemma denominator_not_dvd (b:ℚ) (j:Fin 3) (hg:p∉badPrimes)
    (hd:p∈(forms b.num b.den (shift j)).natAbs.primeFactors) : ¬(p:ℤ)∣(b.den:ℤ) := by
  intro hb
  have hform:(p:ℤ)∣forms b.num b.den (shift j) := Int.natCast_dvd.mpr (Nat.mem_primeFactors.mp hd).2.1
  have hprod:(p:ℤ)∣coefficient j*b.num := by
    rw [form_linear] at hform
    have hh:=dvd_sub hform (dvd_mul_of_dvd_right hb (offset j))
    simpa only [add_sub_cancel_right] using hh
  have hpZ:Prime (p:ℤ):=Nat.prime_iff_prime_int.mp Fact.out
  have ha:(p:ℤ)∣b.num := (hpZ.dvd_mul.mp hprod).resolve_left (coefficient_not_dvd p hg j)
  exact hpZ.not_unit ((Rat.isCoprime_num_den b).isUnit_of_dvd' ha hb)

lemma mapped_contact (b:ℚ) (j:Fin 3) (hg:p∉badPrimes)
    (hp:p∈(forms b.num b.den (shift j)).natAbs.primeFactors)
    (ho:Odd (padicValInt p (forms b.num b.den (shift j)))) :
    ∃f:ℤ,rationalPlace p (b-root j.castSucc)=f ∧ 0<f ∧ Odd f := by
  have hfne : forms b.num b.den (shift j)≠0 := by
    have hh : (forms b.num b.den (shift j)).natAbs≠0 := (Nat.mem_primeFactors.mp hp).2.2
    simpa only [Int.natAbs_ne_zero] using hh
  have hb:=denominator_not_dvd p b j hg hp
  have hbval:rationalPlace p (b.den:ℚ)=0 := by
    rw [rational_value p _ (by exact_mod_cast b.den_nz)]
    change ((padicValRat p ((b.den:ℤ):ℚ):ℤ):WithTop ℤ)=0
    rw [padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hb]
    norm_num
  have hfv:rationalPlace p (forms b.num b.den (shift j):ℚ)=
      ((padicValInt p (forms b.num b.den (shift j)):ℤ):WithTop ℤ) := by
    rw [rational_value p _ (by exact_mod_cast hfne),padicValRat.of_int]
  rw [form_identity,(rationalPlace p).map_mul,(rationalPlace p).map_mul,
    coefficient_unit p hg j,hbval,zero_add,zero_add] at hfv
  refine ⟨_,hfv,?_,?_⟩
  · have hh:padicValInt p (forms b.num b.den (shift j))≠0 := by
      intro hz
      rw [hz] at ho
      norm_num at ho
    exact_mod_cast Nat.pos_of_ne_zero hh
  · exact_mod_cast ho

/-- The extra 1/2 scalar factor is a unit at all three consumed finite
contacts. Exact collision primes359 and4801 are excluded, not ignored. -/
lemma selected_polynomial_contact (hg:p∉badPrimes) (b:ℚ) (i:Fin 4) (f:ℤ)
    (hf:rationalPlace p (b-root i)=f) (hpos:0<f) :
    rationalPlace p (polynomial b)=f := by
  have htpos:0 < rationalPlace p (b-root i) := by rw [hf]; exact_mod_cast hpos
  have hothers:∀j:Fin 4,j≠i→ rationalPlace p (b-root j)=0 := by
    intro j hji
    have hu:=difference_unit p hg i j hji.symm
    have he:b-root j=(b-root i)+(root i-root j) := by ring
    rw [he,(rationalPlace p).map_add_eq_of_lt_right (by rw [hu]; exact htpos)]
    exact hu
  have h64:rationalPlace p (64:ℚ)=0 :=
    supported_unit p _ (by norm_num) hg (by norm_num [modulus]) (by norm_num [modulus])
  rw [polynomial_product,(rationalPlace p).map_mul,h64,zero_add,
    FiniteContact318.value_prod (rationalPlace p),Finset.sum_eq_single i]
  · exact hf
  · intro j hj hji; exact hothers j hji
  · simp

/-- Every actual scalar radical prime is a positive odd contact of the
literal decoded four-factor r. Zero/infinity parity and all collisions are
fully discharged; the order8 index theorem is a separate downstream step. -/
theorem member_source_contact (S:ℚ) (w:Assignment) (source:Constraints (stage0 S) w)
    (hb:beta w≠0) (hp:p∈scalarPrimes w) :
    ∃f:ℤ,rationalPlace p (r w)=f ∧ 0<f ∧ Odd f := by
  obtain ⟨j,hj0,hj1,hp,hg,ho⟩ := member_nonzero_noninfinite p w hb hp
  have hj : j=2 ∨ j=3 ∨ j=4 := by fin_cases j <;> simp_all
  have hm (k:Fin 3) (hp:p∈(forms (beta w).num (beta w).den (shift k)).natAbs.primeFactors)
      (ho:Odd (padicValInt p (forms (beta w).num (beta w).den (shift k)))) :
      ∃f:ℤ,rationalPlace p (r w)=f ∧ 0<f ∧ Odd f := by
    obtain ⟨f,hf,hpos,hodd⟩ := mapped_contact p (beta w) k hg hp ho
    refine ⟨f,?_,hpos,hodd⟩
    rw [r_formula S w source]
    exact selected_polynomial_contact p hg (beta w) k.castSucc f hf hpos
  rcases hj with rfl|rfl|rfl
  · exact hm 0 hp ho
  · exact hm 1 hp ho
  · exact hm 2 hp ho

#print axioms difference_support
#print axioms polynomial_product
#print axioms form_linear
#print axioms form_identity
#print axioms coefficient_nonzero
#print axioms good_modulus
#print axioms not_dvd_supported
#print axioms supported_unit
#print axioms difference_unit
#print axioms coefficient_not_dvd
#print axioms coefficient_unit
#print axioms denominator_not_dvd
#print axioms mapped_contact
#print axioms selected_polynomial_contact
#print axioms member_source_contact
end ScalarContactValuation318
