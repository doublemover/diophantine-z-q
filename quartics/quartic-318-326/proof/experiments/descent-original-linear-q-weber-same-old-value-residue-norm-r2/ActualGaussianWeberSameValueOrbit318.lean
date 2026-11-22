module
public import ActualGaussianWeberQuarterTurn318
public import ActualGaussianWeberValueOrbitAlgebra318
public section
noncomputable section

namespace ActualGaussianWeberSameValueOrbit318

open WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberValueOrbitAlgebra318

variable {K : Type*} [Field K] [DecidableEq K]

@[expose] def squaredAbscissa : WP K → Option K
  | .zero => none
  | .some x _ _ => some (x^2)

private theorem weber_negY (x y : K) : (curve K).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY,curve,WeierstrassCurve.toAffine]

private theorem point_neg_some (x y : K)
    (h : (curve K).toAffine.Nonsingular x y) :
    -Point.some x y h =
      Point.some x (-y) (by
        have h0 : (curve K).toAffine.Nonsingular x ((curve K).toAffine.negY x y) :=
          (nonsingular_neg ..).mpr h
        rwa [weber_negY] at h0) := by
  rw [Point.neg_some]
  exact some_transport rfl (weber_negY x y)

/-- The equality criterion for the actual Weber value on stock
points: only the true coordinate turns appear. The point at infinity
forms its own orbit and the proof covers possible repeated turns. -/
theorem same_weber_value (h2 : (2:K)≠0) (i : K) (hi : i^2= -1) (P Q : WP K) :
    squaredAbscissa Q = squaredAbscissa P ↔
      Q=P ∨ Q= -P ∨ Q=turn h2 i hi P ∨ Q= -turn h2 i hi P := by
  constructor
  · intro h
    cases P with
    | zero =>
      cases Q with
      | zero => exact Or.inl rfl
      | some u v hn =>
        change (some (u^2) : Option K) = none at h
        cases h
    | some x y hp =>
      cases Q with
      | zero =>
        change (none : Option K) = some (x^2) at h
        cases h
      | some u v hq =>
        change (some (u^2) : Option K) = some (x^2) at h
        have e := (same_value_iff i hi x y u v
          ((literal_equation x y).mp hp.1) ((literal_equation u v).mp hq.1)).mp
          (Option.some.inj h)
        rcases e with h|h|h|h
        · exact Or.inl (some_transport h.1 h.2)
        · apply Or.inr
          apply Or.inl
          rw [point_neg_some]
          exact some_transport h.1 h.2
        · apply Or.inr
          apply Or.inr
          apply Or.inl
          rw [turn_some]
          exact some_transport h.1 h.2
        · apply Or.inr
          apply Or.inr
          apply Or.inr
          rw [turn_some,point_neg_some]
          exact some_transport h.1 h.2
  · rintro (rfl|rfl|rfl|rfl)
    · rfl
    · cases P with
      | zero => rfl
      | some x y hn => rw [point_neg_some] <;> rfl
    · cases P with
      | zero => rfl
      | some x y hn => simp only [turn_some,squaredAbscissa,neg_sq]
    · cases P with
      | zero => rfl
      | some x y hn => simp only [turn_some,point_neg_some,squaredAbscissa,neg_sq]

end ActualGaussianWeberSameValueOrbit318
