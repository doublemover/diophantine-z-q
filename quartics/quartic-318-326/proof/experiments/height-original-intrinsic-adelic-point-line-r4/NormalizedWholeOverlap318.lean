module
public import NormalizedReciprocalLaurent318
public import DVRNormalizedAllPlaceCharts318
public section
noncomputable section
namespace NormalizedWholeOverlap318
open Polynomial NormalizedReciprocalLaurent318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)
abbrev FiniteOrder := DVRNormalizedFiniteOrder318.Order R d a
abbrev InfinityOrder := DVRNormalizedInfinityOrder318.Order R d a
@[expose] def finiteParameter (i : Fin 4) : Laurent R :=
  algebraMap R[X] (Laurent R) (DVRNormalizedFiniteOrder318.coefficient R d a i)
@[expose] def infinityParameter (i : Fin 4) : Laurent R :=
  reciprocalMap R (DVRNormalizedInfinityOrder318.coefficient R d a i)

theorem parameter_identity (i : Fin 4) :
    finiteParameter R d a i=infinityParameter R d a i*(coordinate R:Laurent R)^2 := by
  have hC (r : R) : algebraMap R[X] (Laurent R) (C r)=algebraMap R (Laurent R) r :=
    (IsScalarTower.algebraMap_apply R R[X] (Laurent R) r).symm
  simp only [finiteParameter,infinityParameter,DVRNormalizedFiniteOrder318.coefficient,
    DVRNormalizedInfinityOrder318.coefficient,map_mul,map_sub,map_one,hC,
    reciprocalMap,Polynomial.aeval_C,Polynomial.aeval_X,←coordinate_value]
  calc
    _ = algebraMap R (Laurent R) (d i) *
      (((coordinate R:Laurent R)*(↑(coordinate R)⁻¹:Laurent R))*
        ((coordinate R:Laurent R)-algebraMap R (Laurent R) (a i)*
          ((coordinate R:Laurent R)*(↑(coordinate R)⁻¹:Laurent R)))) := by
      rw [Units.mul_inv]
      ring
    _ = _ := by ring

/-- Both whole punctured four-root orders are equivalent by the actual
y_i=t*v_i scaling. No coefficient, radicand or contact difference is inverted. -/
@[expose] def fullOverlap :
    FourRootOrder318.Order (finiteParameter R d a) ≃ₐ[Laurent R]
      FourRootOrder318.Order (infinityParameter R d a) :=
  FourRootUnitScale318.four _ _ (coordinate R) (parameter_identity R d a)

theorem fullOverlap_generator (i : Fin 4) :
    fullOverlap R d a (FourRootOrderSigns318.generator (finiteParameter R d a) i)=
      (coordinate R:Laurent R) • FourRootOrderSigns318.generator (infinityParameter R d a) i :=
  FourRootUnitScale318.four_generator _ _ _ _ i

@[expose] def finiteBaseChange :
    Laurent R ⊗[R[X]] FiniteOrder R d a ≃ₐ[Laurent R]
      FourRootOrder318.Order (finiteParameter R d a) :=
  FourRootOrder318.baseChange (DVRNormalizedFiniteOrder318.coefficient R d a) (Laurent R)

section Reciprocal
local instance reciprocalAlgebra : Algebra R[X] (Laurent R) := (reciprocalMap R).toRingHom.toAlgebra
@[expose] def infinityBaseChange :
    Laurent R ⊗[R[X]] InfinityOrder R d a ≃ₐ[Laurent R]
      FourRootOrder318.Order (infinityParameter R d a) :=
  FourRootOrder318.baseChange (DVRNormalizedInfinityOrder318.coefficient R d a) (Laurent R)
end Reciprocal
end NormalizedWholeOverlap318
