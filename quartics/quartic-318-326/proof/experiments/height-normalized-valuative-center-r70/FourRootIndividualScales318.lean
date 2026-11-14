module
public import FourRootUnitScale318
public section
noncomputable section
namespace FourRootIndividualScales318
open QuadraticPresentation318 FourRootOrderSigns318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- Each original signed root has its own specified square multiplier.
The full order and its scalar base are retained, even at zero radicands. -/
@[expose] def four (a b : Fin 4 → R) (s : Fin 4 → Rˣ)
    (h : ∀ i,b i=a i*(s i:R)^2) :
    FourRootOrder318.Order b ≃ₐ[R] FourRootOrder318.Order a :=
  Algebra.TensorProduct.congr
    (Algebra.TensorProduct.congr (UnitScaledQuadraticOrder318.equiv (a 0) (b 0) (s 0) (h 0))
      (UnitScaledQuadraticOrder318.equiv (a 1) (b 1) (s 1) (h 1)))
    (Algebra.TensorProduct.congr (UnitScaledQuadraticOrder318.equiv (a 2) (b 2) (s 2) (h 2))
      (UnitScaledQuadraticOrder318.equiv (a 3) (b 3) (s 3) (h 3)))

theorem four_generator (a b : Fin 4 → R) (s : Fin 4 → Rˣ)
    (h : ∀ i,b i=a i*(s i:R)^2) (i : Fin 4) :
    four a b s h (generator b i)=(s i:R) • generator a i := by
  fin_cases i <;> simp [four,generator,Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul,FourRootUnitScale318.root_scale,←Algebra.smul_def,
    TensorProduct.smul_tmul',TensorProduct.tmul_smul]
end FourRootIndividualScales318
