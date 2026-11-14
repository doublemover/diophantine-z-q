module
public import NormalizedWholeGluing318
public import JLineOverlap318
public section
noncomputable section
namespace NormalizedWholeScalarMaps318
open Polynomial NormalizedWholeOverlap318 NormalizedReciprocalLaurent318 NormalizedWholeOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)

theorem finite_polynomial (p : R[X]) :
    finiteMap R d a (algebraMap R[X] (FiniteOrder R d a) p)=
      algebraMap (Laurent R) (CommonOrder R d a) (algebraMap R[X] (Laurent R) p) := by
  change finiteBaseChange R d a (Algebra.TensorProduct.includeRight
    (algebraMap R[X] (FiniteOrder R d a) p))=_
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply R[X] (Laurent R)
    (Laurent R ⊗[R[X]] FiniteOrder R d a),AlgEquiv.commutes]

theorem infinity_polynomial (p : R[X]) :
    infinityMap R d a (algebraMap R[X] (InfinityOrder R d a) p)=
      algebraMap (Laurent R) (CommonOrder R d a) (reciprocalMap R p) := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R).toRingHom.toAlgebra
  change (fullOverlap R d a).symm (infinityBaseChange R d a
    (Algebra.TensorProduct.includeRight (algebraMap R[X] (InfinityOrder R d a) p)))=_
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply R[X] (Laurent R)
    (Laurent R ⊗[R[X]] InfinityOrder R d a),AlgEquiv.commutes,AlgEquiv.commutes]
  all_goals rfl

@[expose] def commonT : (CommonOrder R d a)ˣ :=
  Units.map (algebraMap (Laurent R) (CommonOrder R d a)).toMonoidHom (coordinate R)

theorem finite_evaluation :
    (finiteMap R d a).comp (algebraMap R[X] (FiniteOrder R d a))=
      (Polynomial.aeval (R:=R) (commonT R d a:CommonOrder R d a)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply,finite_polynomial,Polynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply R (Laurent R) (CommonOrder R d a) r).symm
  · rw [RingHom.comp_apply,finite_polynomial,Polynomial.aeval_X]
    change algebraMap (Laurent R) (CommonOrder R d a) (algebraMap R[X] (Laurent R) X)=
      algebraMap (Laurent R) (CommonOrder R d a) (coordinate R:Laurent R)
    rw [coordinate_value]

theorem infinity_evaluation :
    (infinityMap R d a).comp (algebraMap R[X] (InfinityOrder R d a))=
      (Polynomial.aeval (R:=R) (↑(commonT R d a)⁻¹:CommonOrder R d a)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply,infinity_polynomial]
    simp only [reciprocalMap,Polynomial.aeval_C,←IsScalarTower.algebraMap_apply]
  · rw [RingHom.comp_apply,infinity_polynomial,Polynomial.aeval_X]
    change algebraMap (Laurent R) (CommonOrder R d a) (↑(coordinate R)⁻¹:Laurent R)=_
    exact map_units_inv _ _
end NormalizedWholeScalarMaps318
