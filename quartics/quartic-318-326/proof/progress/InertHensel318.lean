module
public import InertSourceExclusion318
public import Mathlib.NumberTheory.Padics.Hensel
public section
namespace InertHensel318
open Polynomial
set_option maxHeartbeats 0
variable (p:ℕ) [Fact p.Prime]

/-- A simple residue root of X²−2 lifts to an actual p-adic square root. -/
theorem square_root_lift (hp2:¬p∣2) (hs:∃x:ZMod p,x^2=2) :
    ∃rho:ℚ_[p],rho^2=2 := by
  obtain ⟨x,hx⟩ := hs
  let n:ℕ := x.val
  have hn:(n:ZMod p)=x := ZMod.natCast_zmod_val x
  have hnunit:¬p∣n := by
    intro h
    have hz:(n:ZMod p)=0 := (ZMod.natCast_eq_zero_iff n p).2 h
    have htwo:(2:ZMod p)=0 := by rw [hn] at hz; simpa [hz] using hx.symm
    exact hp2 ((ZMod.natCast_eq_zero_iff 2 p).1 htwo)
  have hdiv:(p:ℤ)∣(n:ℤ)^2-2 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast
    rw [hn,hx,sub_self]
  have hsmall:‖(n:ℤ_[p])^2-2‖<1 := by
    have hh := (PadicInt.norm_int_lt_one_iff_dvd (p:=p) ((n:ℤ)^2-2)).2 hdiv
    simpa using hh
  have hunit:‖(2:ℤ_[p])*(n:ℤ_[p])‖=1 := by
    rw [norm_mul]
    have h2:‖(2:ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.2
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out:p.Prime)).2 hp2)
    have hn':‖(n:ℤ_[p])‖=1 := PadicInt.norm_natCast_eq_one_iff.2
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out:p.Prime)).2 hnunit)
    rw [h2,hn',one_mul]
  let F:Polynomial ℤ := X^2-C 2
  have heval (z:ℤ_[p]):F.aeval z=z^2-2 := by simp [F]; exact aeval_natCast z 2
  have hder (z:ℤ_[p]):F.derivative.aeval z=2*z := by simp [F,derivative_pow,show (aeval z) (2:Polynomial ℤ)=2 from aeval_natCast z 2]
  obtain ⟨z,hz,-⟩ := hensels_lemma (F:=F) (a:=(n:ℤ_[p]))
    (by rw [heval,hder,hunit,one_pow]; exact hsmall)
  have hz':z^2=2 := sub_eq_zero.mp ((heval z).symm.trans hz)
  refine ⟨(z:ℚ_[p]),?_⟩
  change (↑(z^2):ℚ_[p])=2
  rw [hz']
  rfl
open CircuitReplay Raw318FinalReplay RawWeights318 FiniteContact318
open ConcretePadic318 (rationalPlace)

/-- A consumed contact in chain 0 produces an actual p-adic realization. -/
theorem source_contact0_padic_split (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A0 S w)=a)
    (hf:rationalPlace p (t0 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃rho:ℚ_[p],rho^2=2 := by
  exact square_root_lift p
    (not_dvd_supported p hgood 2 (by norm_num [contactModulus]))
    (InertSourceExclusion318.source_contact0_residue_split p S w source a f j
      hgood hp17 hp41 hA hf hpos hodd)

/-- A consumed contact in chain 1 produces an actual p-adic realization. -/
theorem source_contact1_padic_split (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A1 S w)=a)
    (hf:rationalPlace p (t1 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃rho:ℚ_[p],rho^2=2 := by
  exact square_root_lift p
    (not_dvd_supported p hgood 2 (by norm_num [contactModulus]))
    (InertSourceExclusion318.source_contact1_residue_split p S w source a f j
      hgood hp17 hp41 hA hf hpos hodd)

/-- A consumed contact in chain 2 produces an actual p-adic realization. -/
theorem source_contact2_padic_split (S:ℚ) (w:Assignment)
    (source:Constraints (stage0 S) w) (a f:ℤ) (j:Fin 5)
    (hgood:¬p∣contactModulus) (hp17:¬p∣17) (hp41:¬p∣41)
    (hA:rationalPlace p (A2 S w)=a)
    (hf:rationalPlace p (t2 S w-root j)=f) (hpos:0<f) (hodd:Odd f) :
    ∃rho:ℚ_[p],rho^2=2 := by
  exact square_root_lift p
    (not_dvd_supported p hgood 2 (by norm_num [contactModulus]))
    (InertSourceExclusion318.source_contact2_residue_split p S w source a f j
      hgood hp17 hp41 hA hf hpos hodd)

end InertHensel318
#print axioms InertHensel318.square_root_lift

#print axioms InertHensel318.source_contact0_padic_split

#print axioms InertHensel318.source_contact1_padic_split

#print axioms InertHensel318.source_contact2_padic_split
