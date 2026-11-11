module
public import LocalPullbackUnit318
public import Mathlib.LinearAlgebra.Basis.Basic
public section
noncomputable section
namespace PullbackFrameCoefficient318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)(M:Y.Modules)(U:Y.Opens)
  (e:Γ(Y,U)≃ₗ[Γ(Y,U)]Γ(M,U))
  (p:Γ(X,f⁻¹ᵁU)≃ₗ[Γ(X,f⁻¹ᵁU)]Γ((Scheme.Modules.pullback f).obj M,f⁻¹ᵁU))
  (hp:p 1=LocalPullbackUnit318.pull f M U (e 1))
/-- Once the actual chart-unit comparison pins the generator, the
coefficient of EVERY original local section is its exact pulled scalar.
The normalization hp must come from the actual chart comparison. -/
theorem coefficient(s:Γ(M,U)):
    p.symm (LocalPullbackUnit318.pull f M U s)=f.app U (e.symm s):=by
  have hs:s=(e.symm s) • e 1:=by
    rw [←e.map_smul,smul_eq_mul,mul_one,e.apply_symm_apply]
  rw [hs,LocalPullbackUnit318.pull_smul,←hp,map_smul,p.symm_apply_apply,
    smul_eq_mul,mul_one]
/-- A true base generator stays a true regular generator in the actual
pulled frame, because the original structure map sends units to units. -/
theorem generator_unit(s:Γ(M,U))(hs:IsUnit (e.symm s)):
    IsUnit (p.symm (LocalPullbackUnit318.pull f M U s)):=by
  rw [coefficient f M U e p hp]
  exact hs.map (f.app U).hom
end PullbackFrameCoefficient318
