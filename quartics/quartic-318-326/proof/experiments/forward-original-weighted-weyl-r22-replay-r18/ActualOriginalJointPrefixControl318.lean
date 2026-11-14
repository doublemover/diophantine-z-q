module
public import ActualOriginalFiniteIntegralTriangle318
public section
noncomputable section
namespace ActualOriginalJointPrefixControl318
open MeasureTheory ActualOriginalFiniteAbel318
open scoped BigOperators

/-- Time-dependent separable PHASES, with no separability requirement
on the spatial weight. steps+1 actual terms occur on each axis. -/
structure TimeAxis (E : Type*) where
  step : E
  steps : ℕ
  phase : ℕ → ℝ → ℂ

@[expose] def timeRectangle {E : Type*} [AddMonoid E] (g : E → ℂ) :
    List (TimeAxis E) → E → ℝ → ℂ
  | [], x, _ => g x
  | a::as, x, t => ∑ j∈Finset.range (a.steps+1),
      timeRectangle g as (x+j • a.step) t*a.phase j t

/-- This recursive condition means that EACH joint prefix has an L1
bound. It is not the L1 norm of a pointwise maximum over prefixes. The
integrability witness is retained at the exact phase product. -/
@[expose] def JointPrefixControl {E : Type*} (μ : Measure ℝ) (M : ℝ) :
    List (TimeAxis E) → (ℝ → ℂ) → Prop
  | [], F => Integrable F μ ∧ (∫ t, ‖F t‖ ∂μ)≤M
  | a::as, F => ∀ n≤a.steps+1,
      JointPrefixControl μ M as (fun t => F t*prefix (fun j => a.phase j t) n)

lemma actual_time_rectangle_translation {E : Type*} [AddCommMonoid E]
    (g : E → ℂ) (v : E) (as : List (TimeAxis E)) : ∀ x t,
    timeRectangle (fun z => g (z+v)) as x t=timeRectangle g as (x+v) t := by
  induction as with
  | nil => intro x t; rfl
  | cons a as ih =>
    intro x t
    simp only [timeRectangle,ih]
    apply Finset.sum_congr rfl
    intro j hj
    congr 2
    ac_rfl

lemma actual_time_rectangle_sub {E : Type*} [AddMonoid E]
    (g g' : E → ℂ) (as : List (TimeAxis E)) : ∀ x t,
    timeRectangle (fun z => g z-g' z) as x t=
      timeRectangle g as x t-timeRectangle g' as x t := by
  induction as with
  | nil => intro x t; rfl
  | cons a as ih =>
    intro x t
    simp only [timeRectangle,ih,sub_mul,Finset.sum_sub_distrib]

/-- Backward boundary coefficient has exactly the norm of the forward
mixed difference. Its sign cannot change the coefficient budget. -/
lemma actual_time_rectangle_backward {E : Type*} [AddCommMonoid E]
    (g : E → ℂ) (v : E) (as : List (TimeAxis E)) (x : E) (t : ℝ) :
    timeRectangle (fun z => g z-g (z+v)) as x t=
      timeRectangle g as x t-timeRectangle g as (x+v) t := by
  rw [actual_time_rectangle_sub,actual_time_rectangle_translation]

end ActualOriginalJointPrefixControl318
