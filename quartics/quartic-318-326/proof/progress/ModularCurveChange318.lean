module
public import ModularWeierstrass318
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public section
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
namespace ModularCurveChange318
set_option maxHeartbeats 0

@[expose] def modularImage : Subgroup (GL (Fin 2) ℝ) := (Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ).range

/-- The variable-change convention rescales coefficients by u^{-4},u^{-6},
so the actual change from the tau model to the gamma*tau model has u=1/(c*tau+d). -/
@[expose] def change (gamma:GL (Fin 2) ℝ) (tau:UpperHalfPlane) : WeierstrassCurve.VariableChange ℂ where
  u := (Units.mk0 (denom gamma tau) (denom_ne_zero gamma tau))⁻¹
  r := 0
  s := 0
  t := 0

theorem E4_transform (gamma:GL (Fin 2) ℝ) (hgamma:gamma∈modularImage) (tau:UpperHalfPlane) :
    ModularForm.E₄ (gamma • tau)=denom gamma tau^4*ModularForm.E₄ tau := by
  have he:=SlashInvariantForm.slash_action_eqn''
    (Γ:=(Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ).range) ModularForm.E₄ hgamma tau
  simpa only [zpow_ofNat] using he

theorem E6_transform (gamma:GL (Fin 2) ℝ) (hgamma:gamma∈modularImage) (tau:UpperHalfPlane) :
    ModularForm.E₆ (gamma • tau)=denom gamma tau^6*ModularForm.E₆ tau := by
  have he:=SlashInvariantForm.slash_action_eqn''
    (Γ:=(Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ).range) ModularForm.E₆ hgamma tau
  simpa only [zpow_ofNat] using he

/-- Equality of the actual transformed Weierstrass models, not only their j-invariants. -/
theorem curve_change (gamma:GL (Fin 2) ℝ) (hgamma:gamma∈modularImage) (tau:UpperHalfPlane) :
    change gamma tau • ModularWeierstrass318.curve tau=
      ModularWeierstrass318.curve (gamma • tau) := by
  rw [ModularWeierstrass318.curve,ModularWeierstrass318.curve,E4_transform gamma hgamma tau,
    E6_transform gamma hgamma tau]
  ext <;> simp [change,WeierstrassCurve.variableChange_def,NormalizedWeierstrass318.model] <;> ring

/-- The inverse change also holds as an actual group action on curves. -/
theorem inverse_curve_change (gamma:GL (Fin 2) ℝ) (hgamma:gamma∈modularImage) (tau:UpperHalfPlane) :
    (change gamma tau)⁻¹ • ModularWeierstrass318.curve (gamma • tau)=
      ModularWeierstrass318.curve tau := by
  rw [←curve_change gamma hgamma tau,inv_smul_smul]
/-- Direct unconditional SL2(Z) specialization of the actual curve change. -/
theorem sl_curve_change (gamma:SL(2,ℤ)) (tau:UpperHalfPlane) :
    change ((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) gamma) tau •
      ModularWeierstrass318.curve tau =
      ModularWeierstrass318.curve (((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) gamma) • tau) :=
  curve_change _ ⟨gamma,rfl⟩ tau
end ModularCurveChange318
#print axioms ModularCurveChange318.curve_change
