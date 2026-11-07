module
public import NormalizedWeierstrass318
public import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
public import ActualQJ318
public section
noncomputable section
namespace ModularWeierstrass318
set_option maxHeartbeats 0

/-- The actual normalized complex elliptic model associated to the genuine
weight-four and weight-six Eisenstein values. -/
@[expose] def curve (tau : UpperHalfPlane) : WeierstrassCurve ℂ :=
  NormalizedWeierstrass318.model (ModularForm.E₄ tau) (ModularForm.E₆ tau)

theorem curve_c4 (tau : UpperHalfPlane) : (curve tau).c₄ = ModularForm.E₄ tau :=
  NormalizedWeierstrass318.model_c4 _ _

theorem curve_c6 (tau : UpperHalfPlane) : (curve tau).c₆ = ModularForm.E₆ tau :=
  NormalizedWeierstrass318.model_c6 _ _

/-- The actual Weierstrass discriminant equals the genuine modular eta^24
discriminant; the E4/E6 identity is proved in Mathlib, not assumed here. -/
theorem curve_discriminant (tau : UpperHalfPlane) :
    (curve tau).Δ = ModularForm.discriminant tau := by
  rw [curve, NormalizedWeierstrass318.model_discriminant,
    ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]

theorem curve_discriminant_ne_zero (tau : UpperHalfPlane) : (curve tau).Δ ≠ 0 := by
  rw [curve_discriminant]
  exact ModularForm.discriminant_ne_zero tau

instance curve_isElliptic (tau : UpperHalfPlane) : (curve tau).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (curve_discriminant_ne_zero tau)⟩

/-- Actual algebraic j of the normalized complex elliptic model equals the
actual modular j used by the analytic qj producer. -/
theorem curve_j (tau : UpperHalfPlane) :
    (curve tau).j = ActualQJ318.jInvariant tau := by
  rw [WeierstrassCurve.j_eq, curve_discriminant, curve_c4]
  unfold ActualQJ318.jInvariant
  ring

/-- The actual holomorphic qj producer binds to the actual Weierstrass j. -/
theorem G_qParam_curve_j (tau : UpperHalfPlane) :
    ActualQJ318.G (Function.Periodic.qParam 1 tau) =
      Function.Periodic.qParam 1 tau * (curve tau).j := by
  rw [curve_j]
  exact ActualQJ318.G_qParam tau

end ModularWeierstrass318
