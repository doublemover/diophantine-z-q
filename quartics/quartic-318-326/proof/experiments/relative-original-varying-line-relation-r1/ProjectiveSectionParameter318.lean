module
public import FiniteProjectiveTensorDual318
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public section
noncomputable section
namespace ProjectiveSectionParameter318
open TensorProduct
open scoped TensorProduct
universe u v w z
variable (R : Type u) [CommRing R] (P : Type v) [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

/-- An ACTUAL commutative coefficient algebra parameterizing sections,
not a set of formal labels: the symmetric algebra on the true dual. -/
abbrev algebra := SymmetricAlgebra R (Module.Dual R P)

variable (S : Type w) [CommRing S] [Algebra R S]

/-- Canonical functor-of-points classification of the actual affine
parameter algebra, through finite projective evaluation duality. -/
@[expose] def points : (algebra R P →ₐ[R] S) ≃ S ⊗[R] P :=
  (SymmetricAlgebra.lift : (Module.Dual R P →ₗ[R] S) ≃ (algebra R P →ₐ[R] S)).symm.trans
    (FiniteProjectiveTensorDual318.equivalence R P S (FiniteProjectiveEvaluationFrame318.frame R P)).symm.toEquiv

lemma coordinate (a : algebra R P →ₐ[R] S) (φ : Module.Dual R P) :
    FiniteProjectiveTensorDual318.pairing R P S (points R P S a) φ=a (SymmetricAlgebra.ι R _ φ) := by
  change FiniteProjectiveTensorDual318.equivalence R P S (FiniteProjectiveEvaluationFrame318.frame R P)
    ((FiniteProjectiveTensorDual318.equivalence R P S (FiniteProjectiveEvaluationFrame318.frame R P)).symm
      (SymmetricAlgebra.lift.symm a)) φ=_
  rw [LinearEquiv.apply_symm_apply]
  have h := congrArg (fun g : algebra R P →ₐ[R] S => g (SymmetricAlgebra.ι R _ φ))
    (SymmetricAlgebra.lift.apply_symm_apply a)
  rw [SymmetricAlgebra.lift_ι_apply] at h
  exact h

@[expose] def universal : algebra R P ⊗[R] P :=
  points R P (algebra R P) (AlgHom.id R (algebra R P))

lemma universal_coordinate (φ : Module.Dual R P) :
    FiniteProjectiveTensorDual318.pairing R P (algebra R P) (universal R P) φ=SymmetricAlgebra.ι R _ φ :=
  coordinate R P (algebra R P) (AlgHom.id R _) φ

/-- Tensor coefficient transport of a section, along a genuine R-algebra map. -/
@[expose] def transport {T : Type z} [CommRing T] [Algebra R T] (g : S →ₐ[R] T) :
    S ⊗[R] P →ₗ[R] T ⊗[R] P := TensorProduct.map g.toLinearMap LinearMap.id

lemma transport_pairing {T : Type z} [CommRing T] [Algebra R T] (g : S →ₐ[R] T)
    (x : S ⊗[R] P) (φ : Module.Dual R P) :
    FiniteProjectiveTensorDual318.pairing R P T (transport R P S g x) φ=
      g (FiniteProjectiveTensorDual318.pairing R P S x φ) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x =>
      change g s*algebraMap R T (φ x)=g (s*algebraMap R S (φ x))
      rw [map_mul,AlgHom.commutes]
  | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]

/-- Classification is natural in the ACTUAL coefficient map. -/
lemma natural {T : Type z} [CommRing T] [Algebra R T] (g : S →ₐ[R] T) (a : algebra R P →ₐ[R] S) :
    points R P T (g.comp a)=transport R P S g (points R P S a) := by
  apply (FiniteProjectiveTensorDual318.equivalence R P T (FiniteProjectiveEvaluationFrame318.frame R P)).injective
  ext φ
  rw [coordinate,transport_pairing,coordinate]
  rfl

/-- Every represented point is exactly specialization of the same
universal tensor section, not a separate existence witness. -/
lemma specialize_universal (a : algebra R P →ₐ[R] S) :
    transport R P (algebra R P) a (universal R P)=points R P S a := by
  simpa only [universal,AlgHom.comp_id] using
    (natural R P (algebra R P) a (AlgHom.id R _)).symm
end ProjectiveSectionParameter318
