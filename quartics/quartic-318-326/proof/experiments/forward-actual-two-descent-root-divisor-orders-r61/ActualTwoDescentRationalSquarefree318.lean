module
public import ActualTwoDescentSignedActualProducer318
public section
noncomputable section
namespace ActualTwoDescentRationalSquarefree318
open ActualTwoDescentPrimeMonomials318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actual_even_of_zero_bit (z : ℤ) (hz : (z : ZMod 2)=0) : Even z := by
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).mp hz
  exact ⟨k,by omega⟩

lemma actual_monomial_outside_valuation (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (u : ι → ZMod 2) (q : ℕ) [Fact q.Prime] (hq : ∀ i, q ≠ p i) :
    padicValRat q (monomial p u : ℚ)=0 := by
  rw [padicValRat.of_nat,monomial,actual_valuation_product]
  · have hs : (∑ i, padicValNat q (p i^(u i).val))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [padicValNat.pow,padicValNat_primes (hq i),mul_zero]
    rw [hs,Int.natCast_zero]
  · intro i
    exact pow_ne_zero _ (Fact.out : (p i).Prime).ne_zero

/-- Every positive rational squareclass with even valuation outside a
specified distinct prime support has a LITERAL binary monomial representative.
Only the global rational-square criterion is used, not a local-to-global
assertion for elliptic curves. -/
theorem actual_positive_supported_rational (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (x : ℚ) (hx : 0<x)
    (H : ∀ q : ℕ, q.Prime → (∀ i, q ≠ p i) → Even (padicValRat q x)) :
    ∃ u : ι → ZMod 2, ∃ r : ℚ, r ≠ 0 ∧ x=(monomial p u : ℚ)*r^2 := by
  let u : ι → ZMod 2 := fun i => (padicValRat (p i) x : ZMod 2)
  have hM : 0 < (monomial p u : ℚ) := by exact_mod_cast monomial_pos p u
  have hq : 0 < x/(monomial p u : ℚ) := div_pos hx hM
  have hs : IsSquare (x/(monomial p u : ℚ)) := by
    apply Rat.isSquare_iff_even_factorization.mpr
    refine ⟨hq.le,?_⟩
    intro q hprime
    letI : Fact q.Prime := ⟨hprime⟩
    rw [padicValRat.div hx.ne' hM.ne']
    by_cases he : ∃ i, p i=q
    · obtain ⟨i,rfl⟩ := he
      apply actual_even_of_zero_bit
      rw [Int.cast_sub,actual_monomial_valuation_bit p hd u i]
      exact sub_self _
    · have hout : ∀ i, q ≠ p i := fun i h => he ⟨i,h.symm⟩
      rw [actual_monomial_outside_valuation p u q hout,sub_zero]
      exact H q hprime hout
  obtain ⟨r,hr⟩ := hs
  have hr0 : r ≠ 0 := by
    intro he
    rw [he,mul_zero] at hr
    exact hq.ne' hr
  refine ⟨u,r,hr0,?_⟩
  calc
    x=(monomial p u : ℚ)*(x/(monomial p u : ℚ)) := by field_simp [hM.ne']
    _=(monomial p u : ℚ)*r^2 := by rw [hr,pow_two]

/-- The sign is the only extra rational squareclass coordinate. -/
theorem actual_signed_supported_rational (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (x : ℚ) (hx : x ≠ 0)
    (H : ∀ q : ℕ, q.Prime → (∀ i, q ≠ p i) → Even (padicValRat q x)) :
    ∃ (ε : ZMod 2) (u : ι → ZMod 2), ∃ r : ℚ, r ≠ 0 ∧
      x=(-1 : ℚ)^ε.val*(monomial p u : ℚ)*r^2 := by
  by_cases hp : 0<x
  · obtain ⟨u,r,hr,he⟩ := actual_positive_supported_rational p hd x hp H
    exact ⟨0,u,r,hr,by simpa using he⟩
  · have hn : 0 < -x := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hx)
    have Hn : ∀ q : ℕ, q.Prime → (∀ i, q ≠ p i) → Even (padicValRat q (-x)) := by
      intro q hq hout
      rw [padicValRat.neg]
      exact H q hq hout
    obtain ⟨u,r,hr,he⟩ := actual_positive_supported_rational p hd (-x) hn Hn
    refine ⟨1,u,r,hr,?_⟩
    norm_num
    linarith [he]

end ActualTwoDescentRationalSquarefree318
