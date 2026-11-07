module
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace NormalizedWeierstrass318
set_option maxHeartbeats 0

/-- The actual short Weierstrass model with prescribed c4 and c6 invariants. -/
@[expose] def model (c4 c6 : ℂ) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -c4/48
  a₆ := -c6/864

theorem model_c4 (c4 c6 : ℂ) : (model c4 c6).c₄ = c4 := by
  simp [model, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem model_c6 (c4 c6 : ℂ) : (model c4 c6).c₆ = c6 := by
  simp [model, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

theorem model_discriminant (c4 c6 : ℂ) :
    (model c4 c6).Δ = (c4^3-c6^2)/1728 := by
  have h := (model c4 c6).c_relation
  rw [model_c4, model_c6] at h
  linear_combination h/1728

theorem model_j (c4 c6 : ℂ) [(model c4 c6).IsElliptic] :
    (model c4 c6).j = c4^3 / ((c4^3-c6^2)/1728) := by
  rw [WeierstrassCurve.j_eq, model_discriminant, model_c4]
  ring

end NormalizedWeierstrass318
