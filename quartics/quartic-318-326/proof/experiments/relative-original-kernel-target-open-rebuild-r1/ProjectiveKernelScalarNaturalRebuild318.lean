module
public import ProjectiveKernelScalarActionRebuild318
public section
noncomputable section
namespace ProjectiveKernelScalarNaturalRebuild318
open AlgebraicGeometry
variable (R P Q : Type*) [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
variable {S T : Type*} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
lemma natural (g : S →ₐ[R] T) (t : S)
    (a : ProjectiveKernelParameter318.algebra R P Q d →ₐ[R] S) :
    g.comp (ProjectiveKernelScalarActionRebuild318.pointScale R P Q d S t a) =
      ProjectiveKernelScalarActionRebuild318.pointScale R P Q d T (g t) (g.comp a) := by
  apply Ideal.Quotient.algHom_ext
  rw [AlgHom.comp_assoc,ProjectiveKernelScalarActionRebuild318.ambient,
    ProjectiveKernelScalarActionRebuild318.ambient,ProjectiveParameterUnitAction318.pointScale_natural,
    AlgHom.comp_assoc]
end ProjectiveKernelScalarNaturalRebuild318
