module
public import ProjectiveKernelScalarActionRebuild318
public import ProjectivePrincipalOriginalPointRebuild318
public import ProjectiveKernelSliceOriginalRebuild318
public import ProjectiveKernelPrincipalCartesian318
public section
noncomputable section
namespace ProjectiveKernelNormalizedPointScaleRebuild318
open AlgebraicGeometry CategoryTheory
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
variable (i : Fin F.size) (S : CommRingCat.{0}) [Algebra R S]
local notation "D" => ProjectiveKernelNormalizedAlgebras318.principalRing R P Q d i
local notation "E" => ProjectiveKernelNormalizedAlgebras318.points R P Q d i S
local notation "qh" => ProjectiveKernelNormalizedAlgebras318.principalQuotient R P Q d i
local notation "qb" => ProjectiveKernelNormalizedAlgebras318.sliceQuotient R P Q d i
local notation "q" => ProjectiveKernelParameter318.quotient R P Q d
/-- Exact original-point equation of normalization on every coefficient
ring, with the full ideal and the literal test-ring unit. -/
lemma original_scaled (a : D →ₐ[R] S) :
    a.comp (ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i) =
      ProjectiveKernelScalarActionRebuild318.pointScale R P Q d S ((E a).1:S)
        ((E a).2.comp (ProjectiveKernelSliceOriginalRebuild318.intoAlgebra R P Q d i)) := by
  apply Ideal.Quotient.algHom_ext
  change (a.comp (ProjectiveKernelPrincipalCartesian318.intoAlgebra R P Q d i)).comp q =
    (ProjectiveKernelScalarActionRebuild318.pointScale R P Q d S ((E a).1:S)
      ((E a).2.comp (ProjectiveKernelSliceOriginalRebuild318.intoAlgebra R P Q d i))).comp q
  rw [ProjectiveKernelScalarActionRebuild318.ambient,
    AlgHom.comp_assoc,ProjectiveKernelPrincipalCartesian318.intoAlgebra_comp,
    AlgHom.comp_assoc,ProjectiveKernelSliceOriginalRebuild318.into_quotient]
  change (a.comp qh).comp (ProjectiveParameterPrincipalNormalization318.point R P i) =
    ProjectiveParameterUnitAction318.pointScale R P S ((E a).1:S)
      (((E a).2.comp qb).comp (Ideal.Quotient.mkₐ R (ProjectiveParameterSliceAlgebra318.ideal R P i)))
  rw [ProjectiveKernelNormalizedAlgebras318.slice_quotient]
  exact ProjectivePrincipalOriginalPointRebuild318.original R P i S (a.comp qh)
end ProjectiveKernelNormalizedPointScaleRebuild318
