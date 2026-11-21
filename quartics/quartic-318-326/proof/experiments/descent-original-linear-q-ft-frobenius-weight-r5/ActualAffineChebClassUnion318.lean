module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic
public section
noncomputable section
namespace ActualAffineChebClassUnion318
open scoped BigOperators
open Classical

/-- Each X is ONE original key on the same rectangle. The product uses
once-counted merged forms; only the finite class label varies per form. -/
theorem same_key_class_sum {X V : Type*} [Fintype V] {J : V → Type*}
    [∀ i, Fintype (J i)] (S : Finset X) (w : (i : V) → J i → X → ℝ) :
    (∑ x ∈ S, ∏ i : V, ∑ j : J i, w i j x) =
      ∑ c : (i : V) → J i, ∑ x ∈ S, ∏ i : V, w i (c i) x := by
  calc
    _ = ∑ x ∈ S, ∑ c : (i : V) → J i, ∏ i : V, w i (c i) x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Fintype.prod_sum (fun i j => w i j x)
    _ = _ := Finset.sum_comm

/-- Taking a finite union never needs uniformity in a growing ray field.
For a fixed set of class tuples, the exact error is bounded by their
sum rather than by an exchange with the next wheel cutoff. -/
theorem summed_affine_error {J : Type*} [Fintype J] (actual main err : J → ℝ)
    (h : ∀ j, |actual j-main j| ≤ err j) :
    |(∑ j : J, actual j)-(∑ j : J, main j)| ≤ ∑ j : J, err j := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : J, |actual j-main j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum (fun j _ => h j)

/-- Pointwise selector of a finite true partition. The tag is the SINGLE
arithmetic Frobenius conjugacy class of the argument, when unramified. -/
@[expose] def part {J : Type*} [DecidableEq J] (tag : Option J) (value : ℝ) (j : J) : ℝ :=
  if tag = some j then value else 0

theorem sum_parts {J : Type*} [Fintype J] [DecidableEq J] (tag : Option J) (value : ℝ) :
    (∑ j : J, part tag value j) = if tag.isSome then value else 0 := by
  cases tag with
  | none => simp [part]
  | some j =>
    simp only [part,Option.some.injEq,Option.isSome_some,ite_true]
    rw [Finset.sum_eq_single j]
    · simp
    · intro c hc he
      exact if_neg (Ne.symm he)
    · exact (fun h => (h (Finset.mem_univ j)).elim)

end ActualAffineChebClassUnion318
