module
public import IntegralWholeReciprocalGluing318
public import JLineOverlap318
public section
noncomputable section
namespace IntegralWholeOrderScalarMaps318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318 IntegralWholeOrderOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- The original finite scalar inclusion remains fixed through the whole
order base-change equivalence. -/
theorem finite_polynomial (p : R[X]) :
    finiteMap R c (algebraMap R[X] (FiniteOrder R c) p)=
      algebraMap (Laurent R) (CommonOrder R c) (algebraMap R[X] (Laurent R) p) := by
  change finiteBaseChange R c
    (Algebra.TensorProduct.includeRight (algebraMap R[X] (FiniteOrder R c) p)) = _
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply R[X] (Laurent R)
    (Laurent R ⊗[R[X]] FiniteOrder R c),AlgEquiv.commutes]

/-- The reciprocal scalar action is literal evaluation at u=c0/y0. -/
theorem infinity_polynomial (p : R[X]) :
    infinityMap R c (algebraMap R[X] (InfinityOrder R c) p)=
      algebraMap (Laurent R) (CommonOrder R c) (reciprocalMap R c p) := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R c).toRingHom.toAlgebra
  change (fullOverlap R c).symm
    (infinityBaseChange R c
      (Algebra.TensorProduct.includeRight (algebraMap R[X] (InfinityOrder R c) p))) = _
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply R[X] (Laurent R)
    (Laurent R ⊗[R[X]] InfinityOrder R c),AlgEquiv.commutes,AlgEquiv.commutes]
  rfl

@[expose] def commonY : (CommonOrder R c)ˣ :=
  Units.map (algebraMap (Laurent R) (CommonOrder R c)).toMonoidHom (y R)

/-- The reciprocal target coordinate is 1/y0=u/c0, so the chosen projective
line really has y0 as its finite coordinate. -/
@[expose] def infinityProjection : R[X] →ₐ[R] InfinityOrder R c :=
  Polynomial.aeval (algebraMap R (InfinityOrder R c) (↑(c 0)⁻¹:R)*
    algebraMap R[X] (InfinityOrder R c) X)

theorem finite_evaluation :
    (finiteMap R c).comp (algebraMap R[X] (FiniteOrder R c))=
      (Polynomial.aeval (R:=R) (commonY R c:CommonOrder R c)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply,finite_polynomial,Polynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply R (Laurent R) (CommonOrder R c) r).symm
  · rw [RingHom.comp_apply,finite_polynomial,Polynomial.aeval_X]
    change algebraMap (Laurent R) (CommonOrder R c) (algebraMap R[X] (Laurent R) X)=
      algebraMap (Laurent R) (CommonOrder R c) (y R:Laurent R)
    rw [y_value]

theorem infinity_evaluation :
    (infinityMap R c).comp (infinityProjection R c).toRingHom=
      (Polynomial.aeval (R:=R) (↑(commonY R c)⁻¹:CommonOrder R c)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change infinityMap R c (infinityProjection R c (C r))=_
    rw [infinityProjection,Polynomial.aeval_C]
    change infinityMap R c (algebraMap R[X] (InfinityOrder R c) (C r))=_
    rw [infinity_polynomial]
    simp only [reciprocalMap,Polynomial.aeval_C,←IsScalarTower.algebraMap_apply]
  · change infinityMap R c (infinityProjection R c X)=_
    rw [infinityProjection,Polynomial.aeval_X,map_mul]
    change infinityMap R c (algebraMap R[X] (InfinityOrder R c) (C (↑(c 0)⁻¹:R))) *
      infinityMap R c (algebraMap R[X] (InfinityOrder R c) X)=_
    rw [infinity_polynomial,infinity_polynomial]
    simp only [reciprocalMap,Polynomial.aeval_C,Polynomial.aeval_X,u,map_mul,
      ←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul,commonY,Units.coe_map,Units.map_inv]
end IntegralWholeOrderScalarMaps318
