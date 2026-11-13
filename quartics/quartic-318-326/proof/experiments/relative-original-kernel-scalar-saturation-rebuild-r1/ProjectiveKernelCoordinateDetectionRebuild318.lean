module
public import ProjectiveKernelParameter318
public import ProjectiveParameterZeroCoordinates318
public section
noncomputable section
namespace ProjectiveKernelCoordinateDetectionRebuild318
open scoped TensorProduct
universe u v
variable (R P Q : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
abbrev coordinate (i : Fin F.size) : ProjectiveKernelParameter318.algebra R P Q d :=
  ProjectiveKernelParameter318.quotient R P Q d
    (ProjectiveParameterZeroCoordinates318.coordinate R P i)
variable (S : Type v) [CommRing S] [Algebra R S]
lemma value_zero_iff (a : ProjectiveKernelParameter318.algebra R P Q d →ₐ[R] S) :
    (ProjectiveKernelParameter318.points R P Q d S a).val = 0 ↔
      ∀ i, a (coordinate R P Q d i) = 0 := by
  change ProjectiveSectionParameter318.points R P S
    (a.comp (ProjectiveKernelParameter318.quotient R P Q d)) = 0 ↔ _
  exact ProjectiveParameterZeroCoordinates318.zero_iff R P S _
lemma kernel_zero_iff (a : ProjectiveKernelParameter318.algebra R P Q d →ₐ[R] S) :
    ProjectiveKernelParameter318.points R P Q d S a = 0 ↔
      ∀ i, a (coordinate R P Q d i) = 0 := by
  rw [← value_zero_iff R P Q d S a]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h
lemma nonzero_iff (a : ProjectiveKernelParameter318.algebra R P Q d →ₐ[R] S) :
    ProjectiveKernelParameter318.points R P Q d S a ≠ 0 ↔
      ∃ i, a (coordinate R P Q d i) ≠ 0 := by
  rw [kernel_zero_iff]
  exact not_forall
end ProjectiveKernelCoordinateDetectionRebuild318
