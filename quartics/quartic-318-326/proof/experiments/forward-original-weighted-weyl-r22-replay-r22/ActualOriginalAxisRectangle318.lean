module
public import ActualOriginalMixedTranslation318
public section
noncomputable section
namespace ActualOriginalAxisRectangle318
open scoped BigOperators

/-- An axis has steps+1 actual terms. Empty overlaps are handled before
using these positive rectangles. Phase and cap are independent of weight. -/
structure Axis (E : Type*) where
  step : E
  steps : ℕ
  phase : ℕ → ℂ
  cap : ℝ

@[expose] def axisRectangle {E : Type*} [AddMonoid E]
    (g : E → ℂ) : List (Axis E) → E → ℂ
  | [], x => g x
  | a::as, x => ∑ j∈Finset.range (a.steps+1),
      axisRectangle g as (x+j • a.step)*a.phase j

@[expose] def axisCapProduct {E : Type*} : List (Axis E) → ℝ
  | [] => 1
  | a::as => a.cap*axisCapProduct as

lemma actual_axis_cap_product_nonneg {E : Type*} (as : List (Axis E))
    (ha : ∀ a∈as, 0≤a.cap) : 0≤axisCapProduct as := by
  revert ha
  induction as with
  | nil => intro ha; exact zero_le_one
  | cons a as ih =>
    intro ha
    exact mul_nonneg (ha a List.mem_cons_self) (ih (fun b hb => ha b (List.mem_cons_of_mem a hb)))

lemma actual_rectangle_translation {E : Type*} [AddCommMonoid E]
    (g : E → ℂ) (v : E) (as : List (Axis E)) : ∀ x,
    axisRectangle (fun z => g (z+v)) as x=axisRectangle g as (x+v) := by
  induction as with
  | nil => intro x; rfl
  | cons a as ih =>
    intro x
    simp only [axisRectangle,ih]
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    ac_rfl

lemma actual_rectangle_sub {E : Type*} [AddMonoid E]
    (g g' : E → ℂ) (as : List (Axis E)) : ∀ x,
    axisRectangle (fun z => g z-g' z) as x=axisRectangle g as x-axisRectangle g' as x := by
  induction as with
  | nil => intro x; rfl
  | cons a as ih =>
    intro x
    simp only [axisRectangle,ih,sub_mul,Finset.sum_sub_distrib]

lemma actual_rectangle_step {E : Type*} [AddCommMonoid E]
    (g : E → ℂ) (v : E) (as : List (Axis E)) (x : E) :
    axisRectangle (fun z => g (z+v)-g z) as x=
      axisRectangle g as (x+v)-axisRectangle g as x := by
  rw [actual_rectangle_sub,actual_rectangle_translation]

end ActualOriginalAxisRectangle318
