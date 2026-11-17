module
public import FlatKernelBaseChange318
public import ProjectiveKernelNaturality318
public section
noncomputable section
namespace FlatKernelCoefficientNaturality318
open scoped TensorProduct
universe u
variable (R P Q : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] (d : P →ₗ[R] Q)
  (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Module.Flat R S] [Module.Flat R T] (g : S →ₐ[R] T)

/-- The actual flat kernel comparison is natural in the literal tensor
coefficient map, with its original inclusion into the source module. -/
lemma natural (x : S ⊗[R] LinearMap.ker d) :
    FlatKernelBaseChange318.equivalence R P Q d T
      (ProjectiveSectionParameter318.transport R (LinearMap.ker d) S g x)=
    ProjectiveKernelNaturality318.transport R P Q d S g
      (FlatKernelBaseChange318.equivalence R P Q d S x) := by
  apply Subtype.ext
  change (LinearMap.ker d).subtype.baseChange T
    (TensorProduct.map g.toLinearMap LinearMap.id x)=
      TensorProduct.map g.toLinearMap LinearMap.id
        ((LinearMap.ker d).subtype.baseChange S x)
  induction x using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add,hx,hy]
end FlatKernelCoefficientNaturality318
