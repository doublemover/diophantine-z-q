module
public import ProjectiveSectionParameter318
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public section
noncomputable section
namespace ProjectiveKernelEquations318
open scoped TensorProduct
universe u v
variable (R P Q : Type u) [CommRing R] [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] (d : P →ₗ[R] Q)
  (S : Type v) [CommRing S] [Algebra R S]

/-- The genuine base-changed differential is detected by the original duals. -/
lemma differential_pairing (x : S ⊗[R] P) (φ : Module.Dual R Q) :
    FiniteProjectiveTensorDual318.pairing R Q S (d.baseChange S x) φ =
      FiniteProjectiveTensorDual318.pairing R P S x (φ.comp d) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]

variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]

/-- These are actual linear equations in the symmetric algebra of the true dual. -/
@[expose] def equation (φ : Module.Dual R Q) : ProjectiveSectionParameter318.algebra R P :=
  SymmetricAlgebra.ι R _ (φ.comp d)

lemma evaluate_equation (a : ProjectiveSectionParameter318.algebra R P →ₐ[R] S)
    (φ : Module.Dual R Q) :
    a (equation R P Q d φ) = FiniteProjectiveTensorDual318.pairing R Q S
      (d.baseChange S (ProjectiveSectionParameter318.points R P S a)) φ := by
  rw [differential_pairing]
  exact (ProjectiveSectionParameter318.coordinate R P S a (φ.comp d)).symm

/-- Vanishing of ALL equations is equivalent to membership in the actual tensor kernel,
without any flatness assumption on the test algebra. -/
lemma equations_iff (a : ProjectiveSectionParameter318.algebra R P →ₐ[R] S) :
    (∀ φ, a (equation R P Q d φ)=0) ↔
      d.baseChange S (ProjectiveSectionParameter318.points R P S a)=0 := by
  constructor
  · intro h
    apply (FiniteProjectiveTensorDual318.equivalence R Q S
      (FiniteProjectiveEvaluationFrame318.frame R Q)).injective
    ext φ
    change FiniteProjectiveTensorDual318.pairing R Q S
      (d.baseChange S (ProjectiveSectionParameter318.points R P S a)) φ =
        FiniteProjectiveTensorDual318.pairing R Q S 0 φ
    rw [← evaluate_equation,map_zero,LinearMap.zero_apply,h φ]
  · intro h φ
    rw [evaluate_equation,h,map_zero,LinearMap.zero_apply]
end ProjectiveKernelEquations318
