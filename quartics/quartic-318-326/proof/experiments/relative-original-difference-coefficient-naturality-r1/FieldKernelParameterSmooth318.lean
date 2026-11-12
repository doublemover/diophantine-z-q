module
public import FieldKernelParameterAlgebraIso318
public import ProjectiveSymmetricSmooth318
public import FiniteProjectiveDualRetract318
public section
noncomputable section
namespace FieldKernelParameterSmooth318
variable (K P Q : Type) [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q] (d : P →ₗ[K] Q)
  [hpfinite : Module.Finite K P] [hqfinite : Module.Finite K Q]

include hpfinite hqfinite in
/-- Smoothness of the SAME full kernel parameter over a FIELD, with no
surjectivity assumption on its differential and no radical replacement. -/
instance smooth : Algebra.Smooth K (ProjectiveKernelParameter318.algebra K P Q d) := by
  let F := FiniteProjectiveEvaluationFrame318.frame K (LinearMap.ker d)
  letI : Module.Finite K (Module.Dual K (LinearMap.ker d)) :=
    (FiniteProjectiveDualRetract318.properties K (LinearMap.ker d) F).1
  letI : Module.Projective K (Module.Dual K (LinearMap.ker d)) :=
    (FiniteProjectiveDualRetract318.properties K (LinearMap.ker d) F).2
  letI : Algebra.Smooth K (ProjectiveSectionParameter318.algebra K (LinearMap.ker d)) :=
    ProjectiveSymmetricSmooth318.smooth K (Module.Dual K (LinearMap.ker d))
  exact Algebra.Smooth.of_equiv (FieldKernelParameterAlgebraIso318.equivalence K P Q d).symm
end FieldKernelParameterSmooth318
