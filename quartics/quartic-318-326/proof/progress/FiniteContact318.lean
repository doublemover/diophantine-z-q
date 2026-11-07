module
public import SourcePadic318
public section
namespace FiniteContact318
open ConcreteG8Domain ConcretePadic318 SourceContact318 SourcePadic318 RawWeights318
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact support of the five finite contacts and their separation from1. -/
@[expose] def contactModulus : ℕ := 2*3*5*7*11*37*109*439*2399
@[expose] def point : Fin 6 → ℚ := ![0,-1/2,-1,1/2399,-32/407,1]
@[expose] def root (j : Fin 5) : ℚ := point j.castSucc

theorem difference_support (i j : Fin 6) (hij : i≠j) :
    (point i-point j)≠0 ∧ (point i-point j).num.natAbs∣contactModulus^8 ∧
      (point i-point j).den∣contactModulus^8 := by
  fin_cases i <;> fin_cases j <;> norm_num [point,contactModulus] at *

variable (p : ℕ) [Fact p.Prime]

theorem not_dvd_supported (hgood : ¬p∣contactModulus) (n : ℕ)
    (hn : n∣contactModulus^8) : ¬p∣n := by
  intro hp
  exact hgood (Nat.Prime.dvd_of_dvd_pow Fact.out (dvd_trans hp hn))

theorem supported_unit (q : ℚ) (hq : q≠0) (hgood : ¬p∣contactModulus)
    (hn : q.num.natAbs∣contactModulus^8) (hd : q.den∣contactModulus^8) :
    rationalPlace p q=0 := by
  rw [rational_value p q hq]
  have hn0 := padicValNat.eq_zero_of_not_dvd (not_dvd_supported p hgood _ hn)
  have hd0 := padicValNat.eq_zero_of_not_dvd (not_dvd_supported p hgood _ hd)
  simp only [padicValRat,padicValInt,hn0,hd0,Int.natCast_zero,sub_self,WithTop.coe_zero]

theorem difference_unit (hgood : ¬p∣contactModulus) (i j : Fin 6) (hij : i≠j) :
    rationalPlace p (point i-point j)=0 := by
  obtain ⟨hne,hn,hd⟩ := difference_support i j hij
  exact supported_unit p _ hne hgood hn hd

theorem polynomial_product (t : ℚ) : contactPolynomial t=∏ j : Fin 5, (t-root j) := by
  norm_num [contactPolynomial,root,point,Fin.prod_univ_succ]
  ring

theorem value_prod {ι : Type*} (v : AddValuation ℚ (WithTop ℤ)) (s : Finset ι) (g : ι → ℚ) :
    v (∏ i ∈ s, g i)=∑ i ∈ s, v (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.prod_insert hi,Finset.sum_insert hi,v.map_mul,ih]

/-- A selected positive contact gives every other factor and delta as units,
so its valuation is exactly the full five-factor valuation. -/
theorem selected_contact (hgood : ¬p∣contactModulus) (t : ℚ) (i : Fin 5) (f : ℤ)
    (hf : rationalPlace p (t-root i)=f) (hpos : 0<f) :
    rationalPlace p (contactPolynomial t)=f ∧ rationalPlace p (t-1)=0 := by
  have htpos : 0<rationalPlace p (t-root i) := by rw [hf]; exact_mod_cast hpos
  have hothers : ∀ j : Fin 5, j≠i → rationalPlace p (t-root j)=0 := by
    intro j hji
    have hu := difference_unit p hgood i.castSucc j.castSucc (by intro h; apply hji; apply Fin.ext; exact (congrArg Fin.val h).symm)
    have heq : t-root j=(t-root i)+(root i-root j) := by ring
    rw [heq,(rationalPlace p).map_add_eq_of_lt_right (by simpa only [root,hu] using htpos)]
    exact hu
  constructor
  · rw [polynomial_product,value_prod (rationalPlace p)]
    rw [Finset.sum_eq_single i]
    · exact hf
    · intro b hb hbi; exact hothers b hbi
    · simp
  · have hu := difference_unit p hgood i.castSucc 5 (by intro h; have hh := congrArg Fin.val h; simp at hh; omega)
    have hu' : rationalPlace p (root i-1)=0 := by simpa [root,point] using hu
    have heq : t-1=(t-root i)+(root i-1) := by ring
    rw [heq,(rationalPlace p).map_add_eq_of_lt_right (by rw [hu']; exact htpos)]
    exact hu'

open CircuitReplay Raw318FinalReplay

/-- Entire literal source-to-contact extraction with no free delta-unit,
weight, leaf-parity, pole or positive-R assumption. -/
theorem source_contact0 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (rho : ℚ_[p]) (hr : rho^2=2) (a f : ℤ) (i : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17)
    (hA : rationalPlace p (A0 S w)=a)
    (hf : rationalPlace p (t0 S w-root i)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧ ((∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1) ∨
      (∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1)) := by
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t0 S w) i f hf hpos
  apply contact0_at_padic p S w source rho hr a f hA
  · rw [F0_actual S w source]; exact hF
  · exact hd
  · exact hodd
  · exact not_dvd_supported p hgood 2 (by norm_num [contactModulus])
  · exact not_dvd_supported p hgood 3 (by norm_num [contactModulus])
  · exact not_dvd_supported p hgood 7 (by norm_num [contactModulus])
  · exact hp17

/-- Entire literal source-to-contact extraction with no free delta-unit,
weight, leaf-parity, pole or positive-R assumption. -/
theorem source_contact1 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (rho : ℚ_[p]) (hr : rho^2=2) (a f : ℤ) (i : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17)
    (hA : rationalPlace p (A1 S w)=a)
    (hf : rationalPlace p (t1 S w-root i)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧ ((∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1) ∨
      (∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1)) := by
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t1 S w) i f hf hpos
  apply contact1_at_padic p S w source rho hr a f hA
  · rw [F1_actual S w source]; exact hF
  · exact hd
  · exact hodd
  · exact not_dvd_supported p hgood 2 (by norm_num [contactModulus])
  · exact not_dvd_supported p hgood 3 (by norm_num [contactModulus])
  · exact not_dvd_supported p hgood 7 (by norm_num [contactModulus])
  · exact hp17

/-- Entire literal source-to-contact extraction with no free delta-unit,
weight, leaf-parity, pole or positive-R assumption. -/
theorem source_contact2 (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (rho : ℚ_[p]) (hr : rho^2=2) (a f : ℤ) (i : Fin 5)
    (hgood : ¬p∣contactModulus) (hp17 : ¬p∣17)
    (hA : rationalPlace p (A2 S w)=a)
    (hf : rationalPlace p (t2 S w-root i)=f) (hpos : 0<f) (hodd : Odd f) :
    0<f-5*a ∧ ((∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1) ∨
      (∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1)) := by
  obtain ⟨hF,hd⟩ := selected_contact p hgood (t2 S w) i f hf hpos
  apply contact2_at_padic p S w source rho hr a f hA
  · rw [F2_actual S w source]; exact hF
  · exact hd
  · exact hodd
  · exact not_dvd_supported p hgood 2 (by norm_num [contactModulus])
  · exact not_dvd_supported p hgood 3 (by norm_num [contactModulus])
  · exact not_dvd_supported p hgood 7 (by norm_num [contactModulus])
  · exact hp17

end FiniteContact318
