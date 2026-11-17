module
public import FourRootOrderSigns318
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public section
noncomputable section
namespace FourRootVanishingFiber318
open QuadraticPresentation318
open scoped TensorProduct
variable {R : Type*} [CommRing R]

/-- An explicit two-element basis, valid even when the radicand vanishes. -/
@[expose] def rootBasis (a : R) : Module.Basis (Fin 2) R (RootRing a) :=
  (QuadraticAlgebra.basis a 0).map (presentationEquiv a).toLinearEquiv

@[simp] theorem rootBasis_zero (a : R) : rootBasis a 0 = 1 := by
  simp [rootBasis]

@[simp] theorem rootBasis_one (a : R) :
    rootBasis a 1 = AdjoinRoot.root (polynomial a) := by
  simp [rootBasis]

/-- Literal tensor basis of the finite flat four-root cover. -/
@[expose] def orderBasis (a : Fin 4 → R) :
    Module.Basis ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) R (FourRootOrder318.Order a) :=
  ((rootBasis (a 0)).tensorProduct (rootBasis (a 1))).tensorProduct
    ((rootBasis (a 2)).tensorProduct (rootBasis (a 3)))

@[expose] def rootIndex : Fin 4 → ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  ![((1,0),(0,0)), ((0,1),(0,0)), ((0,0),(1,0)), ((0,0),(0,1))]

theorem basis_root (a : Fin 4 → R) (i : Fin 4) :
    orderBasis a (rootIndex i) = FourRootOrderSigns318.generator a i := by
  fin_cases i <;> simp [orderBasis, rootIndex, FourRootOrderSigns318.generator]

theorem generator_ne_zero [Nontrivial R] (a : Fin 4 → R) (i : Fin 4) :
    FourRootOrderSigns318.generator a i ≠ 0 := by
  rw [← basis_root]
  exact (orderBasis a).ne_zero (rootIndex i)

/-- If a radicand vanishes in the actual fiber base, its tensor root remains
nonzero but has square zero. Finite flatness does not imply reduced fibers. -/
theorem nonzero_square_zero [Nontrivial R] (a : Fin 4 → R)
    (i : Fin 4) (hi : a i = 0) :
    ∃ x : FourRootOrder318.Order a, x ≠ 0 ∧ x^2 = 0 := by
  refine ⟨FourRootOrderSigns318.generator a i, generator_ne_zero a i, ?_⟩
  rw [FourRootOrderSigns318.generator_square, hi, map_zero]

variable {S : Type*} [CommRing S] [Nontrivial S] [Algebra R S]

/-- The nilpotent occurs in the literal scalar-extension algebra, not merely
in a quotient with an unproved connection to the model's fiber. -/
theorem baseChange_nonzero_square_zero (a : Fin 4 → R) (i : Fin 4)
    (hi : algebraMap R S (a i) = 0) :
    ∃ x : S ⊗[R] FourRootOrder318.Order a, x ≠ 0 ∧ x^2 = 0 := by
  let e := FourRootOrder318.baseChange a S
  obtain ⟨x,hx,hx2⟩ := nonzero_square_zero (fun j => algebraMap R S (a j)) i hi
  refine ⟨e.symm x, ?_, ?_⟩
  · intro h
    apply hx
    have he := congrArg e h
    simpa using he
  · apply e.injective
    simpa using hx2

end FourRootVanishingFiber318
