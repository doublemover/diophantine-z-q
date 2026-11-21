module
public import Mathlib
public section
noncomputable section
namespace ActualTZRegulatedLocalFactor318
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {I X K : Type*} [Fintype I] [DecidableEq I] [Fintype X]
  [Field K] [CharZero K]

abbrev Bits (I : Type*) := I → Bool

@[expose] def pick (z : K) (a : Bool) : K := if a then -z else 1

@[expose] def selected (d e : Bits I) (i : I) : Prop := d i = true ∨ e i = true

@[expose] def accepts (root : I → X) (x : X) (d e : Bits I) : Prop :=
  ∀ i, selected d e i → root i = x

@[expose] def amplitude (z w : I → K) (d e : Bits I) : K :=
  ∏ i : I, pick (z i) (d i) * pick (w i) (e i)

def acceptedMass (root : I → X) (d e : Bits I) : K := by
  classical
  exact (∑ x : X, if accepts root x d e then 1 else 0) / (Fintype.card X : K)

private def gate (root : I → X) (x : X) (z w : I → K) (i : I)
    (d e : Bool) : K := by
  classical
  exact if d = true ∨ e = true then
    if root i = x then pick (z i) d * pick (w i) e else 0
  else 1

private theorem gate_prod (root : I → X) (x : X) (z w : I → K) (d e : Bits I) :
    (∏ i : I, gate root x z w i (d i) (e i)) =
      if accepts root x d e then amplitude z w d e else 0 := by
  classical
  by_cases h : accepts root x d e
  · rw [if_pos h,amplitude]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : selected d e i
    · simp only [gate, if_pos (show d i = true ∨ e i = true from hi),if_pos (h i hi)]
    · have hd : d i = false := by
        cases H : d i <;> simp_all [selected]
      have he : e i = false := by
        cases H : e i <;> simp_all [selected]
      simp [gate,hd,he,pick]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := not_forall.mp h
    have ht := (not_imp.mp hi).1
    have hx := (not_imp.mp hi).2
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [gate, if_pos (show d i = true ∨ e i = true from ht),if_neg hx]

/-- Both divisor slots at one original row may choose the same prime.
The residue constraint is counted once, not once per slot. -/
theorem expand_at_residue (root : I → X) (x : X) (z w : I → K) :
    (∑ d : Bits I,∑ e : Bits I,
      if accepts root x d e then amplitude z w d e else 0) =
      ∏ i : I, if root i = x then (1-z i)*(1-w i) else 1 := by
  classical
  calc
    _ = ∑ d : Bits I, ∑ e : Bits I, ∏ i : I, gate root x z w i (d i) (e i) := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      exact (gate_prod root x z w d e).symm
    _ = ∏ i : I, ∑ d : Bool, ∑ e : Bool, gate root x z w i d e := by
      symm
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [Fintype.prod_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : root i = x
      · simp [Fintype.sum_bool,gate,pick,hi] <;> ring
      · simp [Fintype.sum_bool,gate,pick,hi]

/-- The exact local divisor-pair factor, valid also when distinct
original positions have equal residue roots. Empty classes contribute
zero to the correction: the all-off pair contributes the base 1. -/
theorem residue_factor (root : I → X) [Nonempty X] (z w : I → K) :
    (∑ d : Bits I, ∑ e : Bits I, amplitude z w d e * acceptedMass root d e) =
      1 + (∑ x : X, ((∏ i : I, if root i = x then (1-z i)*(1-w i) else 1)-1)) /
        (Fintype.card X : K) := by
  classical
  have hc : (Fintype.card X : K) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := X)).ne'
  calc
    _ = ((∑ d : Bits I, ∑ e : Bits I, ∑ x : X,
        if accepts root x d e then amplitude z w d e else 0)) / (Fintype.card X : K) := by
      unfold acceptedMass
      simp only [mul_div_assoc,Finset.sum_div,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : accepts root x d e <;> simp [h]
    _ = (∑ x : X, ∏ i : I, if root i = x then (1-z i)*(1-w i) else 1) /
        (Fintype.card X : K) := by
      congr 1
      calc
        _ = ∑ d : Bits I, ∑ x : X, ∑ e : Bits I,
            if accepts root x d e then amplitude z w d e else 0 := by
          apply Finset.sum_congr rfl
          intro d _
          exact Finset.sum_comm
        _ = ∑ x : X, ∑ d : Bits I, ∑ e : Bits I,
            if accepts root x d e then amplitude z w d e else 0 := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          exact expand_at_residue root x z w
    _ = _ := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_one]
      field_simp <;> ring

theorem acceptedMass_eq (root : I → X) [Nonempty X] (d e : Bits I) :
    (acceptedMass root d e : K) = if ∀ i, ¬selected d e i then 1 else
      if ∀ i j, selected d e i → selected d e j → root i = root j
      then 1/(Fintype.card X : K) else 0 := by
  classical
  have hc : (Fintype.card X : K) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := X)).ne'
  by_cases h0 : ∀ i, ¬selected d e i
  · rw [if_pos h0,acceptedMass]
    have h (x : X) : accepts root x d e := fun i hi => (h0 i hi).elim
    simp only [h,if_true,Finset.sum_const,Finset.card_univ,nsmul_one,div_self hc]
  · rw [if_neg h0,acceptedMass]
    obtain ⟨i,hi⟩ : ∃ i,selected d e i := by simpa only [not_forall,not_not] using h0
    by_cases hp : ∀ i j, selected d e i → selected d e j → root i = root j
    · rw [if_pos hp]
      have h (x : X) : accepts root x d e ↔ root i = x :=
        ⟨fun H => H i hi, fun H j hj => (hp j i hj hi).trans H⟩
      simp only [h]
      rw [Finset.sum_eq_single (root i)]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    · rw [if_neg hp]
      have hn (x : X) : ¬accepts root x d e := fun H =>
        hp (fun i j hi hj => (H i hi).trans (H j hj).symm)
      simp only [hn,if_false,Finset.sum_const_zero,zero_div]

/-- At an injective root tuple the correction is the sum of the
individual two-slot corrections. This still includes the term z_i*w_i
when both slots select the same prime at one position. -/
theorem distinct_correction (root : I → X) (hInj : Function.Injective root)
    (z w : I → K) :
    (∑ x : X, ((∏ i : I, if root i = x then (1-z i)*(1-w i) else 1)-1)) =
      ∑ i : I, ((1-z i)*(1-w i)-1) := by
  classical
  let v (i : I) := (1-z i)*(1-w i)
  have hS (x : X) : (∏ i : I, if root i = x then v i else 1)-1 =
      ∑ i : I, if root i = x then v i-1 else 0 := by
    by_cases hr : ∃ i,root i=x
    · obtain ⟨i,hi⟩ := hr
      have off (j : I) (hj : j ≠ i) : root j ≠ x := fun H => hj (hInj (H.trans hi.symm))
      have hp : (∏ j : I, if root j=x then v j else 1) =
          (if root i=x then v i else 1) := by
        apply Finset.prod_eq_single i
        · intro j _ hj
          simp only [if_neg (off j hj)]
        · simp
      have hs : (∑ j : I, if root j=x then v j-1 else 0) =
          (if root i=x then v i-1 else 0) := by
        apply Finset.sum_eq_single i
        · intro j _ hj
          simp only [if_neg (off j hj)]
        · simp
      simp only [hp,hs,hi,if_true]
    · have h (i : I) : root i ≠ x := fun h => hr ⟨i,h⟩
      simp only [if_neg (h _),Finset.prod_const_one,sub_self,Finset.sum_const_zero]
  change (∑ x : X, ((∏ i : I, if root i = x then v i else 1)-1)) = ∑ i : I, v i-1
  simp_rw [hS]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (root i)]
  · simp
  · intro x _ hx
    simp only [if_neg (Ne.symm hx)]
  · simp

/-- Finite product over an independent prime universe (or other local
cells). This expands products of local factors but does not encode the
ordinary coupled cutoff d,e ≤ R. -/
theorem finite_product_expand {P E : Type*} [Fintype P] [DecidableEq P] [Fintype E]
    (w : P → E → K) :
    (∏ p : P, ∑ e : E,w p e) = ∑ a : P → E, ∏ p : P,w p (a p) := by
  rw [Fintype.prod_sum]

end ActualTZRegulatedLocalFactor318
