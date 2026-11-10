module
public import UnitScaledQuadraticOrder318
public import FourRootOrderSigns318
public section
noncomputable section
namespace FourRootUnitScale318
open QuadraticPresentation318 FourRootOrderSigns318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- A full four-root order equivalence under the same signed unit scaling.
Neither the four radicands nor their pairwise differences need to be units. -/
@[expose] def four (a b : Fin 4 → R) (s : Rˣ) (h : ∀ i,b i=a i*(s:R)^2) :
    FourRootOrder318.Order b ≃ₐ[R] FourRootOrder318.Order a :=
  Algebra.TensorProduct.congr
    (Algebra.TensorProduct.congr (UnitScaledQuadraticOrder318.equiv (a 0) (b 0) s (h 0))
      (UnitScaledQuadraticOrder318.equiv (a 1) (b 1) s (h 1)))
    (Algebra.TensorProduct.congr (UnitScaledQuadraticOrder318.equiv (a 2) (b 2) s (h 2))
      (UnitScaledQuadraticOrder318.equiv (a 3) (b 3) s (h 3)))

theorem root_scale (a b : R) (s : Rˣ) (h : b=a*(s:R)^2) :
    UnitScaledQuadraticOrder318.equiv a b s h (AdjoinRoot.root (polynomial b))=
      (s:R) • AdjoinRoot.root (polynomial a) := by
  rw [UnitScaledQuadraticOrder318.equiv_root,Algebra.smul_def]

theorem four_generator (a b : Fin 4 → R) (s : Rˣ)
    (h : ∀ i,b i=a i*(s:R)^2) (i : Fin 4) :
    four a b s h (generator b i)=(s:R) • generator a i := by
  fin_cases i <;> simp [four,generator,Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul,root_scale,←Algebra.smul_def,
    TensorProduct.smul_tmul',TensorProduct.tmul_smul]
end FourRootUnitScale318
