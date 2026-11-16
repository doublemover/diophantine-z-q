module
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic
public section
noncomputable section
namespace PurePowerReductionFiniteSpan318
open Set
variable {ι R A : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A] [Algebra R A]

@[expose] def monomial (x : ι → A) (d : ι → ℕ) : A := ∏ i, x i ^ d i
@[expose] def weight (d : ι → ℕ) : ℕ := ∑ i, d i
lemma monomial_add (x : ι → A) (d e : ι → ℕ) :
    monomial x (d+e) = monomial x d * monomial x e := by
  simp only [monomial,Pi.add_apply,pow_add,Finset.prod_mul_distrib]
lemma monomial_single (x : ι → A) (i : ι) (n : ℕ) :
    monomial x (Pi.single i n) = x i ^ n := by
  classical
  simp [monomial,Pi.single_apply]
lemma weight_add (d e : ι → ℕ) : weight (d+e) = weight d + weight e := by
  simp only [weight,Pi.add_apply,Finset.sum_add_distrib]
lemma weight_single (i : ι) (n : ℕ) : weight (Pi.single i n) = n := by
  classical
  simp [weight,Pi.single_apply]

/-- Simultaneous PURE-power relations with strictly lower TOTAL-degree
remainders give a finite spanning box of monomials. Coefficients are in
the actual base ring, not a fraction field. This is the degree-reduction
input for a whole finite normalization with prescribed first jet. -/
theorem fg_span (x : ι → A) (N : ι → ℕ)
    (hrel : ∀ i, x i ^ N i ∈ Submodule.span R
      {y : A | ∃ d : ι → ℕ, weight d < N i ∧ monomial x d = y}) :
    (Submodule.span R (Set.range (monomial x))).FG := by
  classical
  let box : Set A := Set.range (fun d : ∀ i, Fin (N i) => monomial x (fun i => (d i).val))
  let M : Submodule R A := Submodule.span R box
  have hall : ∀ k : ℕ, ∀ d : ι → ℕ, weight d = k → monomial x d ∈ M := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hdk
      by_cases hb : ∀ i, d i < N i
      · exact Submodule.subset_span ⟨fun i => ⟨d i,hb i⟩,rfl⟩
      · push_neg at hb
        obtain ⟨i,hi⟩ := hb
        let e : ι → ℕ := d - Pi.single i (N i)
        have hde : e + Pi.single i (N i) = d := by
          funext j
          by_cases hj : j = i
          · subst j
            simp only [e,Pi.add_apply,Pi.sub_apply,Pi.single_eq_same]
            exact Nat.sub_add_cancel hi
          · simp only [e,Pi.add_apply,Pi.sub_apply,Pi.single_eq_of_ne hj,Nat.sub_zero,add_zero]
        have hw : weight e + N i = weight d := by
          rw [←hde,weight_add,weight_single]
        have hmul : ∀ y : A, y ∈ Submodule.span R
            {y : A | ∃ v : ι → ℕ, weight v < N i ∧ monomial x v = y} →
              monomial x e * y ∈ M := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨v,hv,rfl⟩ := hy
            rw [←monomial_add]
            apply ih (weight (e+v)) ?_ (e+v) rfl
            rw [weight_add]
            omega
          | zero => simpa only [mul_zero] using M.zero_mem
          | add y z hy hz hy' hz' => simpa only [mul_add] using M.add_mem hy' hz'
          | smul r y hy hy' => simpa only [mul_smul_comm] using M.smul_mem r hy'
        rw [←hde,monomial_add,monomial_single]
        exact hmul _ (hrel i)
  have heq : Submodule.span R (Set.range (monomial x)) = M := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro y ⟨d,rfl⟩
      exact hall (weight d) d rfl
    · apply Submodule.span_le.mpr
      rintro y ⟨d,rfl⟩
      exact Submodule.subset_span ⟨fun i => (d i).val,rfl⟩
  rw [heq]
  exact Submodule.fg_span (Set.finite_range _)
end PurePowerReductionFiniteSpan318
