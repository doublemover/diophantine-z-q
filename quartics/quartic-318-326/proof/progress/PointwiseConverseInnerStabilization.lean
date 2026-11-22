module
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Filter.Finite

public section

open Filter

namespace PointwiseConverseInnerStabilization

universe u v w

variable {ι : Type u}

/-- A finite row has one value on a member of the specified ultrafilter.
No cofinality, arithmetic or chain-complex hypothesis is used here. -/
theorem existsUnique_eventually_value (U : Ultrafilter ι)
    {A : Type v} [Finite A] (row : ι → A) :
    ∃! value : A, ∀ᶠ i in (U : Filter ι), row i = value := by
  have h : ∀ᶠ i in (U : Filter ι), ∃ a : A, row i = a :=
    Filter.Eventually.of_forall (fun i => ⟨row i, rfl⟩)
  obtain ⟨a, ha⟩ :=
    (Ultrafilter.eventually_exists_iff (f := U) (P := fun a i => row i = a)).mp h
  refine ⟨a, ha, ?_⟩
  intro b hb
  obtain ⟨_, hi⟩ := (hb.and ha).exists
  exact hi.1.symm.trans hi.2

noncomputable def stabilizedValue (U : Ultrafilter ι)
    {A : Type v} [Finite A] (row : ι → A) : A :=
  Classical.choose (existsUnique_eventually_value U row).exists

theorem eventually_stabilizedValue (U : Ultrafilter ι)
    {A : Type v} [Finite A] (row : ι → A) :
    ∀ᶠ i in (U : Filter ι), row i = stabilizedValue U row :=
  Classical.choose_spec (existsUnique_eventually_value U row).exists

theorem stabilizedValue_eq_of_eventually (U : Ultrafilter ι)
    {A : Type v} [Finite A] (row : ι → A) {a : A}
    (ha : ∀ᶠ i in (U : Filter ι), row i = a) :
    stabilizedValue U row = a := by
  obtain ⟨_, hi⟩ := ((eventually_stabilizedValue U row).and ha).exists
  exact hi.1.symm.trans hi.2

/-- Stabilization is unaffected by padding or by changing a row off a
member of this same ultrafilter. -/
theorem stabilizedValue_congr (U : Ultrafilter ι)
    {A : Type v} [Finite A] (row row' : ι → A)
    (h : ∀ᶠ i in (U : Filter ι), row i = row' i) :
    stabilizedValue U row = stabilizedValue U row' := by
  apply stabilizedValue_eq_of_eventually U row
  exact (h.and (eventually_stabilizedValue U row')).mono
    (fun _ hi => hi.1.trans hi.2)

/-- Reduction is applied to a stabilized row, using actual eventual
commutation at the original stages as an input. -/
theorem reduce_stabilizedValue (U : Ultrafilter ι)
    {A : Type v} {B : Type w} [Finite A] [Finite B]
    (reduce : B → A) (higher : ι → B) (lower : ι → A)
    (h : ∀ᶠ i in (U : Filter ι), reduce (higher i) = lower i) :
    reduce (stabilizedValue U higher) = stabilizedValue U lower := by
  apply Eq.symm
  apply stabilizedValue_eq_of_eventually U lower
  exact ((eventually_stabilizedValue U higher).and h).mono
    (fun _ hi => hi.2.symm.trans (congrArg reduce hi.1))

/-- All levels have compatible stabilized values under the *one* U.
There is no assertion of a single event on which infinitely many levels
simultaneously stabilize. Adjacent reductions suffice for an indexed tower. -/
theorem existsUnique_compatible_levels (U : Ultrafilter ι)
    (A : ℕ → Type v) [∀ n, Finite (A n)]
    (reduce : ∀ n, A (n + 1) → A n) (row : ∀ n, ι → A n)
    (h : ∀ n, ∀ᶠ i in (U : Filter ι), reduce n (row (n + 1) i) = row n i) :
    ∃! value : (n : ℕ) → A n,
      (∀ n, ∀ᶠ i in (U : Filter ι), row n i = value n) ∧
        (∀ n, reduce n (value (n + 1)) = value n) := by
  refine ⟨(fun n => stabilizedValue U (row n)), ⟨?_, ?_⟩, ?_⟩
  · intro n
    exact eventually_stabilizedValue U (row n)
  · intro n
    exact reduce_stabilizedValue U (reduce n) (row (n + 1)) (row n) (h n)
  · intro value hv
    funext n
    exact (stabilizedValue_eq_of_eventually U (row n) (hv.1 n)).symm

/-- Specialization to cofinal natural-number stages. Rows may be padded
below the precision at which the actual arithmetic datum is defined. -/
theorem existsUnique_compatible_on_tails (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop)
    (A : ℕ → Type v) [∀ n, Finite (A n)]
    (reduce : ∀ n, A (n + 1) → A n) (row : ∀ n, ℕ → A n)
    (h : ∀ n i, n + 1 ≤ i → reduce n (row (n + 1) i) = row n i) :
    ∃! value : (n : ℕ) → A n,
      (∀ n, ∀ᶠ i in (U : Filter ℕ), row n i = value n) ∧
        (∀ n, reduce n (value (n + 1)) = value n) := by
  apply existsUnique_compatible_levels U A reduce row
  intro n
  have htail : ∀ᶠ i in (U : Filter ℕ), n + 1 ≤ i :=
    hU (eventually_ge_atTop (n + 1))
  exact htail.mono (h n)

/-- Finitely many tests, possibly with different value types, do share an
event. This is the finite-diagram interface, not countable completeness. -/
theorem eventually_stabilized_finite_window (U : Ultrafilter ι)
    {J : Type w} [Finite J] (A : J → Type v) [∀ j, Finite (A j)]
    (row : ∀ j, ι → A j) :
    ∀ᶠ i in (U : Filter ι), ∀ j, row j i = stabilizedValue U (row j) := by
  exact Filter.eventually_all.mpr (fun j => eventually_stabilizedValue U (row j))

end PointwiseConverseInnerStabilization
