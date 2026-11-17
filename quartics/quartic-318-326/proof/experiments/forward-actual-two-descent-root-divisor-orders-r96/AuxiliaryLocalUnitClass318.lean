module
public import PadicUnitSquareclass318
public import Mathlib.Data.Nat.GCD.BigOperators
public section
noncomputable section
namespace AuxiliaryLocalUnitClass318
open scoped BigOperators

/-- Removing the chosen prime from the finite parity product gives a unit
at that prime. This supplies E's unit condition in the local construction. -/
theorem prime_product_complement (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ q∈S, q.Prime) (p : ℕ) (hpS : p∈S) :
    (∏ q∈S, q^α q)=p^α p*(∏ q∈S.erase p, q^α q) ∧
      p.Coprime (∏ q∈S.erase p, q^α q) := by
  have hp := hS p hpS
  constructor
  · exact (Finset.mul_prod_erase S (fun q => q^α q) hpS).symm
  · apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    have hqS := (Finset.mem_erase.mp hq).2
    have hqp := (Finset.mem_erase.mp hq).1
    have hnot : ¬p∣q := by
      intro hd
      have he := ((Nat.dvd_prime (hS q hqS)).mp hd).resolve_left hp.ne_one
      exact hqp he.symm
    exact (hp.coprime_iff_not_dvd.mpr hnot).pow_right _

/-- The real-compatible sign does not change the unit property. -/
theorem signed_complement_unit (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ q∈S, q.Prime) (p : ℕ) (hpS : p∈S)
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) :
    ¬(p:ℤ)∣σ*((∏ q∈S.erase p, q^α q):ℕ) := by
  have hp := hS p hpS
  have hc := (prime_product_complement S α hS p hpS).2
  have hn : ¬p∣(∏ q∈S.erase p, q^α q) := hp.coprime_iff_not_dvd.mp hc
  have hz : ¬(p:ℤ)∣((∏ q∈S.erase p, q^α q):ℕ) := by exact_mod_cast hn
  rcases hσ with rfl | rfl <;> simpa using hz


/-- The actual residue class required of the auxiliary prime at a single
place. E is the signed product of the other parity primes, hence a unit.
The integer unit residue is constructed, not supplied. Every integer in
that class transports to the original unit by an actual nonzero square.
At2 the caller uses depth3; elsewhere depth1 suffices. -/
theorem local_unit_class (p : ℕ) [Fact p.Prime] (u : ℤ_[p])
    (hu : ‖u‖=1) (E : ℤ) (hE : ¬(p:ℤ)∣E)
    (k : ℕ) (hk : 0<k) (hk2 : p=2 → 3≤k) :
    ∃ n : ℕ, ¬p∣n ∧ ∀ m : ℤ, (p:ℤ)^k∣m-(n:ℤ) →
      ∃ s : ℚ_[p], s≠0 ∧ (E:ℚ_[p])*(m:ℚ_[p])=(u:ℚ_[p])*s^2 := by
  have hEnorm : ‖(E:ℤ_[p])‖=1 := by
    apply le_antisymm (PadicInt.norm_le_one _)
    exact le_of_not_gt (fun h => hE (PadicInt.norm_intCast_lt_one_iff.mp h))
  have hEQnorm : ‖(E:ℚ_[p])‖=1 := by
    simpa only [PadicInt.norm_intCast_eq_padic_norm] using hEnorm
  have hE0 : (E:ℚ_[p])≠0 := by
    intro h
    simpa [h] using hEQnorm
  have hrnorm : ‖(u:ℚ_[p])/(E:ℚ_[p])‖=1 := by
    rw [norm_div,←PadicInt.norm_coe,hu,hEQnorm,div_self (by norm_num : (1:ℝ)≠0)]
  let r : ℤ_[p] := ⟨(u:ℚ_[p])/(E:ℚ_[p]),le_of_eq hrnorm⟩
  have hr : ‖r‖=1 := hrnorm
  obtain ⟨n,hn,hrn⟩ := PadicUnitSquareclass318.unit_residue p r hr k hk
  refine ⟨n,hn,?_⟩
  intro m hm
  have hrn' : r-((n:ℤ):ℤ_[p])∈Ideal.span {(p:ℤ_[p])^k} := by
    simpa only [Int.cast_natCast] using hrn
  have hmem := PadicUnitSquareclass318.preserve_residue p r k n m hrn' hm
  have hsq : ∃ s : ℤ_[p], s≠0 ∧ (m:ℤ_[p])=r*s^2 := by
    by_cases hp2 : p=2
    · subst p
      have hd : (2:ℤ_[2])^3∣r-(m:ℤ_[2]) :=
        dvd_trans (pow_dvd_pow (2:ℤ_[2]) (hk2 rfl)) (Ideal.mem_span_singleton.mp hmem)
      exact PadicUnitSquareclass318.dyadic r (m:ℤ_[2]) hr (by simpa only [show (2:ℤ_[2])^3=8 by norm_num] using hd)
    · have hd : (p:ℤ_[p])∣r-(m:ℤ_[p]) :=
        dvd_trans (dvd_pow_self _ (Nat.ne_of_gt hk)) (Ideal.mem_span_singleton.mp hmem)
      exact PadicUnitSquareclass318.odd_prime p hp2 r (m:ℤ_[p]) hr hd
  obtain ⟨s,hs0,hs⟩ := hsq
  have hsQ : (s:ℚ_[p])≠0 := fun h => hs0 (PadicInt.ext (by simpa using h))
  have heq : (m:ℚ_[p])=((u:ℚ_[p])/(E:ℚ_[p]))*(s:ℚ_[p])^2 :=
    congrArg (fun x : ℤ_[p] => (x:ℚ_[p])) hs
  refine ⟨(s:ℚ_[p]),hsQ,?_⟩
  rw [heq]
  field_simp [hE0] <;> ring

/-- Multiplying the four coordinates by the same nonzero local multiplier
transports both binary values to the selected integer value. -/
theorem scale_common_value {F : Type*} [Field F]
    (C D u E m s x z T y : F)
    (hA : x^2-2*z^2=D*u) (hB : C*T^2-6*y^2=D*u)
    (hm : E*m=u*s^2) :
    (x*s)^2-2*(z*s)^2=(D*E)*m ∧
      C*(T*s)^2-6*(y*s)^2=(D*E)*m := by
  constructor
  · calc
      (x*s)^2-2*(z*s)^2=(x^2-2*z^2)*s^2 := by ring
      _=(D*E)*m := by rw [hA]; linear_combination -D*hm
  · calc
      C*(T*s)^2-6*(y*s)^2=(C*T^2-6*y^2)*s^2 := by ring
      _=(D*E)*m := by rw [hB]; linear_combination -D*hm

end AuxiliaryLocalUnitClass318
