module
public import FlatKernelCoefficientNaturality318
public section
noncomputable section
namespace FieldKernelLinearPoints318
universe u
variable (K P Q : Type u) [Field K] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q] (d : P →ₗ[K] Q)
  [Module.Finite K P] [Module.Finite K Q]
local notation "A" => ProjectiveKernelParameter318.algebra K P Q d
local notation "H" => LinearMap.ker d
local notation "B" => ProjectiveSectionParameter318.algebra K H

/-- The SAME kernel parameter over a field is naturally equivalent to
its actual finite-dimensional kernel's linear parameter on EVERY algebra,
not only reduced tests or field extensions. -/
@[expose] def points (S : Type u) [CommRing S] [Algebra K S] :
    (A →ₐ[K] S) ≃ (B →ₐ[K] S) :=
  (ProjectiveKernelParameter318.points K P Q d S).trans
    ((FlatKernelBaseChange318.equivalence K P Q d S).symm.toEquiv.trans
      (ProjectiveSectionParameter318.points K H S).symm)

lemma coordinate (S : Type u) [CommRing S] [Algebra K S] (a : A →ₐ[K] S) :
    ProjectiveSectionParameter318.points K H S (points K P Q d S a)=
      (FlatKernelBaseChange318.equivalence K P Q d S).symm
        (ProjectiveKernelParameter318.points K P Q d S a) :=
  (ProjectiveSectionParameter318.points K H S).apply_symm_apply _

lemma natural (S T : Type u) [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    (g : S →ₐ[K] T) (a : A →ₐ[K] S) :
    points K P Q d T (g.comp a)=g.comp (points K P Q d S a) := by
  apply (ProjectiveSectionParameter318.points K H T).injective
  rw [coordinate,ProjectiveSectionParameter318.natural,coordinate]
  apply (FlatKernelBaseChange318.equivalence K P Q d T).injective
  rw [LinearEquiv.apply_symm_apply,FlatKernelCoefficientNaturality318.natural,
    LinearEquiv.apply_symm_apply,ProjectiveKernelNaturality318.natural]
end FieldKernelLinearPoints318
