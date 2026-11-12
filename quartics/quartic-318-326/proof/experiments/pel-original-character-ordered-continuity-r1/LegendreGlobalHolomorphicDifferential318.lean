module
public import LegendreDifferentialChartTransitions318
public section
noncomputable section
namespace LegendreGlobalHolomorphicDifferential318
open Set
open LegendreCompletedComplexAtlas318 LegendreInvariantChartUnits318
open LegendreDifferentialChartTransitions318
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]
abbrev ChartIndex := Finite l ⊕ Infinite l

/-- A holomorphic cotangent section described in the ACTUAL independent
completed atlas. The derivative cocycle is part of the definition, so
unrelated local nonzero coefficients do not constitute a global form. -/
structure HolomorphicDifferential where
  coefficient : ChartIndex l → ℂ → ℂ
  analytic : ∀ i,AnalyticOnNhd ℂ (coefficient i) (localChart l i).target
  transition : ∀ i j z,z∈(Transition l i j).source →
    coefficient i z=coefficient j (Transition l i j z)*deriv (Transition l i j) z

@[expose] def originalCoefficient : ChartIndex l → ℂ→ℂ :=
  Sum.elim (finiteForm l) (infinityForm l)

/-- The actual dx/(2y) form, extended using dy/P'(x) at finite branch
points and the forced native infinity coefficient -dU/J. All four types
of actual chart transition have been proved, not supplied as hypotheses. -/
@[expose] def invariantDifferential : HolomorphicDifferential l where
  coefficient := originalCoefficient l
  analytic i := by
    cases i with
    | inl p => exact finiteForm_analytic l p
    | inr p => exact infinityForm_analytic l p
  transition i j z hz := by
    cases i with
    | inl p =>
      cases j with
      | inl q => exact finite_finite l p q z hz
      | inr q => exact finite_infinity l p q z hz
    | inr p =>
      cases j with
      | inl q => exact infinity_finite l p q z hz
      | inr q => exact infinity_infinity l p q z hz

/-- Nonvanishing on the full atlas, including every finite branch point
and the actual infinity origin. It is not merely generically nonzero. -/
theorem nowhere_zero (i : ChartIndex l) (z : ℂ)
    (hz : z∈(localChart l i).target) :
    (invariantDifferential l).coefficient i z≠0 := by
  cases i with
  | inl p => exact finiteForm_ne_zero l p z hz
  | inr p => exact infinityForm_ne_zero l p z hz

/-- Evaluation on a tangent coordinate in any actual chart. -/
@[expose] def evaluation (i : ChartIndex l) (p : LegendrePlaneOverlap318.CompletedPlane l) :
    ℂ →ₗ[ℂ] ℂ :=
  ((invariantDifferential l).coefficient i (localChart l i p)) • LinearMap.id

/-- The coordinate evaluations are one genuine cotangent value: the
actual chart Jacobian carries every tangent coordinate to the other
chart, and the value is unchanged. -/
theorem evaluation_compatible (i j : ChartIndex l)
    (p : LegendrePlaneOverlap318.CompletedPlane l)
    (hi : p∈(localChart l i).source) (hj : p∈(localChart l j).source) (v : ℂ) :
    evaluation l i p v=evaluation l j p
      (deriv (Transition l i j) (localChart l i p)*v) := by
  have hz : localChart l i p∈(Transition l i j).source := by
    refine ⟨(localChart l i).map_source hi,?_⟩
    simpa only [(localChart l i).left_inv hi] using hj
  have ht := (invariantDifferential l).transition i j (localChart l i p) hz
  have he : Transition l i j (localChart l i p)=localChart l j p := by
    change localChart l j ((localChart l i).symm (localChart l i p))=localChart l j p
    rw [(localChart l i).left_inv hi]
  rw [he] at ht
  change (invariantDifferential l).coefficient i (localChart l i p)*v=
    (invariantDifferential l).coefficient j (localChart l j p)*
      (deriv (Transition l i j) (localChart l i p)*v)
  rw [ht,mul_assoc]

theorem evaluation_ne_zero (i : ChartIndex l)
    (p : LegendrePlaneOverlap318.CompletedPlane l) (hi : p∈(localChart l i).source) :
    evaluation l i p≠0 := by
  intro he
  have h := LinearMap.congr_fun he 1
  have hz := nowhere_zero l i (localChart l i p) ((localChart l i).map_source hi)
  apply hz
  simpa [evaluation] using h

/-- Every point of the same completed algebraic curve has a nonzero
cotangent value, with actual chart overlap compatibility above. -/
theorem every_point (p : LegendrePlaneOverlap318.CompletedPlane l) :
    ∃i,p∈(localChart l i).source ∧ evaluation l i p≠0 := by
  obtain ⟨i,hi⟩:=covers l p
  exact ⟨i,hi,evaluation_ne_zero l i p hi⟩
end LegendreGlobalHolomorphicDifferential318
