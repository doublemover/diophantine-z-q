module
public import ProjectiveKernelParameter318
public import ProjectiveParameterUnitAction318
public section
noncomputable section
namespace ProjectiveKernelScalarActionRebuild318
open scoped TensorProduct
universe u v
variable (R P Q : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
variable (S : Type v) [CommRing S] [Algebra R S]
local notation "K" => ProjectiveKernelParameter318.algebra R P Q d
local notation "E" => ProjectiveKernelParameter318.points R P Q d S
/-- All coefficient-ring scalars act on the SAME full quotient parameter;
this definition needs projectivity of the presentation terms, not H0. -/
def pointScale (t : S) (a : K →ₐ[R] S) : K →ₐ[R] S := E.symm (t • E a)
lemma points_pointScale (t : S) (a : K →ₐ[R] S) :
    E (pointScale R P Q d S t a) = t • E a := E.apply_symm_apply _
lemma pointScale_one (a : K →ₐ[R] S) : pointScale R P Q d S 1 a = a := by
  apply E.injective
  rw [points_pointScale,one_smul]
lemma pointScale_mul (t v : S) (a : K →ₐ[R] S) :
    pointScale R P Q d S t (pointScale R P Q d S v a) =
      pointScale R P Q d S (t*v) a := by
  apply E.injective
  rw [points_pointScale,points_pointScale,points_pointScale,mul_smul]
/-- The scalar action agrees with the original symmetric-algebra action
before taking the full kernel quotient. -/
lemma ambient (t : S) (a : K →ₐ[R] S) :
    (pointScale R P Q d S t a).comp (ProjectiveKernelParameter318.quotient R P Q d) =
      ProjectiveParameterUnitAction318.pointScale R P S t
        (a.comp (ProjectiveKernelParameter318.quotient R P Q d)) := by
  apply (ProjectiveSectionParameter318.points R P S).injective
  rw [ProjectiveParameterUnitAction318.points_pointScale]
  exact congrArg Subtype.val (points_pointScale R P Q d S t a)
end ProjectiveKernelScalarActionRebuild318
