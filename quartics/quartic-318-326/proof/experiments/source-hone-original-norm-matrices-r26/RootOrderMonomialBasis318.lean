module
public import FourRootSignBaseChange318
public import ThreeRootCoordinates318
public import Mathlib.LinearAlgebra.TensorProduct.Basis

public section
noncomputable section
namespace RootOrderMonomialBasis318
open QuadraticPresentation318
open scoped TensorProduct BigOperators
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- The original quadratic presentation has the explicit basis one, root. -/
@[expose] def rootBasis (a : R) : Module.Basis (Fin 2) R (RootRing a) :=
  (QuadraticAlgebra.basis a 0).map (presentationEquiv a).toLinearEquiv

theorem rootBasis_apply (a : R) (i : Fin 2) :
    rootBasis a i = AdjoinRoot.root (polynomial a) ^ (i : ℕ) := by
  fin_cases i <;> simp [rootBasis, Module.Basis.map_apply]

abbrev FourIndex := (Fin 2 × Fin 2) × (Fin 2 × Fin 2)
abbrev ThreeIndex := Fin 2 × (Fin 2 × Fin 2)

/-- All sixteen original four-root tensor monomials, with unique coefficients. -/
@[expose] def fourBasis (a : Fin 4 → R) :
    Module.Basis FourIndex R (FourRootOrder318.Order a) :=
  ((rootBasis (a 0)).tensorProduct (rootBasis (a 1))).tensorProduct
    ((rootBasis (a 2)).tensorProduct (rootBasis (a 3)))

/-- All eight original three-root tensor monomials, with unique coefficients. -/
@[expose] def threeBasis (a : Fin 3 → R) :
    Module.Basis ThreeIndex R (ThreeRootOrder318.Order a) :=
  (rootBasis (a 0)).tensorProduct ((rootBasis (a 1)).tensorProduct (rootBasis (a 2)))

theorem fourBasis_apply (a : Fin 4 → R) (i : FourIndex) :
    fourBasis a i =
      ((AdjoinRoot.root (polynomial (a 0)) ^ (i.1.1 : ℕ)) ⊗ₜ[R]
       (AdjoinRoot.root (polynomial (a 1)) ^ (i.1.2 : ℕ))) ⊗ₜ[R]
      ((AdjoinRoot.root (polynomial (a 2)) ^ (i.2.1 : ℕ)) ⊗ₜ[R]
       (AdjoinRoot.root (polynomial (a 3)) ^ (i.2.2 : ℕ))) := by
  rcases i with ⟨⟨i,j⟩,⟨k,l⟩⟩
  simp only [fourBasis, Module.Basis.tensorProduct_apply, rootBasis_apply]

theorem threeBasis_apply (a : Fin 3 → R) (i : ThreeIndex) :
    threeBasis a i = (AdjoinRoot.root (polynomial (a 0)) ^ (i.1 : ℕ)) ⊗ₜ[R]
      ((AdjoinRoot.root (polynomial (a 1)) ^ (i.2.1 : ℕ)) ⊗ₜ[R]
       (AdjoinRoot.root (polynomial (a 2)) ^ (i.2.2 : ℕ))) := by
  rcases i with ⟨i,⟨j,k⟩⟩
  simp only [threeBasis, Module.Basis.tensorProduct_apply, rootBasis_apply]

/-- The tensor-basis entries are the already existing original named root monomials. -/
theorem fourBasis_monomial (a : Fin 4 → R) (i : FourIndex) :
    fourBasis a i =
      FourRootOrderSigns318.generator a 0 ^ (i.1.1 : ℕ) *
      FourRootOrderSigns318.generator a 1 ^ (i.1.2 : ℕ) *
      FourRootOrderSigns318.generator a 2 ^ (i.2.1 : ℕ) *
      FourRootOrderSigns318.generator a 3 ^ (i.2.2 : ℕ) := by
  simp [fourBasis_apply, FourRootOrderSigns318.generator,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.one_def]

theorem threeBasis_monomial (a : Fin 3 → R) (i : ThreeIndex) :
    threeBasis a i =
      ThreeRootCoordinates318.generator a 0 ^ (i.1 : ℕ) *
      ThreeRootCoordinates318.generator a 1 ^ (i.2.1 : ℕ) *
      ThreeRootCoordinates318.generator a 2 ^ (i.2.2 : ℕ) := by
  simp [threeBasis_apply, ThreeRootCoordinates318.generator,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.TensorProduct.one_def]

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Changing the coefficient ring keeps every original monomial, not only the rank. -/
theorem four_coefficientMap (a : Fin 4 → R) (i : FourIndex) :
    FourRootSignBaseChange318.coefficientMap a S (fourBasis a i) =
      fourBasis (fun j => algebraMap R S (a j)) i := by
  simp only [fourBasis_monomial, map_mul, map_pow,
    FourRootSignBaseChange318.coefficientMap_generator]

theorem three_coefficientMap (a : Fin 3 → R) (i : ThreeIndex) :
    ThreeRootCoordinates318.coefficientMap a S (threeBasis a i) =
      threeBasis (fun j => algebraMap R S (a j)) i := by
  simp only [threeBasis_monomial, map_mul, map_pow,
    ThreeRootCoordinates318.coefficientMap_generator]

end RootOrderMonomialBasis318
