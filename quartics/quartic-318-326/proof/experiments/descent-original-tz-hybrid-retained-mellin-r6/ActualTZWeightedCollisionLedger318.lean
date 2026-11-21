module
public import Mathlib
public section
noncomputable section
namespace ActualTZWeightedCollisionLedger318
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Conditional degree induction step: bad outer specimens have
conditional probability at most one; on every other specimen use
the genuine inner-fibre bound, with no conditional distribution after
conditioning on a wrap or a bad event. -/
theorem weighted_fibre {Z : Type*} [Fintype Z] (m f : Z→ℝ) (bad : Z→Prop) (V : ℝ)
    (hm : ∀ z,0≤m z) (hm1 : (∑ z : Z,m z)=1) (hV : 0≤V)
    (hf : ∀ z,f z≤1) (hg : ∀ z,¬bad z→f z≤V) :
    (∑ z : Z,m z*f z) ≤ V+∑ z : Z,m z*(if bad z then 1 else 0) := by
  classical
  calc
    _ ≤ ∑ z : Z,m z*(V+(if bad z then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (hm z)
      by_cases hz : bad z
      · simp only [if_pos hz]
        linarith [hf z]
      · simpa only [if_neg hz,add_zero] using hg z hz
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,hm1,one_mul]

/-- An indicator bound proved before wrap selection transfers to
actual nonnegative wrap weights |I_r(z)|/n≤1, without ever making a
claim about the conditional distribution of a polynomial on a wrap. -/
theorem wrap_indicators {Z R : Type*} [Fintype Z] [Fintype R]
    (m : Z→ℝ) (θ : Z→R→ℝ) (hit : Z→R→Prop) (C : ℝ)
    (hm : ∀ z,0≤m z) (hθ : ∀ z r,θ z r≤1)
    (h : ∀ r,(∑ z : Z,m z*(if hit z r then 1 else 0))≤C) :
    (∑ z : Z,m z*(∑ r : R,θ z r*(if hit z r then 1 else 0))) ≤ (Fintype.card R:ℝ)*C := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ r : R, (∑ z : Z,m z*(if hit z r then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (hm z)
      by_cases hz : hit z r
      · simpa only [if_pos hz,mul_one] using hθ z r
      · simp only [if_neg hz,mul_zero,le_refl]
    _ ≤ ∑ _r : R,C := Finset.sum_le_sum (fun r _ => h r)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

/-- Exact finite average of the telescoped prime sum. The prime event
can be an actual signed wrapped pair difference; the concentration
bound is asserted before this estimate, not deduced by independence. -/
theorem prime_average {Z P : Type*} [Fintype Z] (Q : Finset P) (m ℓ : Z→ℝ)
    (v C : P→ℝ) (hit : Z→P→Prop) (hm : ∀ z,0≤m z)
    (hv : ∀ p∈Q,0≤v p)
    (hPoint : ∀ z,ℓ z≤∑ p∈Q,v p*(if hit z p then 1 else 0))
    (hEvent : ∀ p∈Q,(∑ z : Z,m z*(if hit z p then 1 else 0))≤C p) :
    (∑ z : Z,m z*ℓ z) ≤ ∑ p∈Q,v p*C p := by
  classical
  calc
    _ ≤ ∑ z : Z,m z*(∑ p∈Q,v p*(if hit z p then 1 else 0)) :=
      Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hPoint z) (hm z))
    _ = ∑ p∈Q,v p*(∑ z : Z,m z*(if hit z p then 1 else 0)) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ _ := Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hEvent p hp) (hv p hp)

end ActualTZWeightedCollisionLedger318
