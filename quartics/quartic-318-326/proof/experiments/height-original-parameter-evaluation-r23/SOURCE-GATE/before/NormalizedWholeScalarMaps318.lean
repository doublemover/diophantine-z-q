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
universe u

/-- Scalar compatibility of the original base-change map, proved before
specializing a carrier with competing polynomial algebra structures. -/
private lemma baseChangedOrderMapAlong_scalar {S T : Type u}
    [CommRing S] [CommRing T] (f : S →+* T) (b : Fin 4 → S) (p : S) :
    baseChangedOrderMapAlong f b (algebraMap S (FourRootOrder318.Order b) p) =
      algebraMap T (FourRootOrder318.Order (fun i => f (b i))) (f p) := by
  letI : Algebra S T := f.toAlgebra
  change (FourRootOrder318.baseChange b T)
    (Algebra.TensorProduct.includeRight (algebraMap S (FourRootOrder318.Order b) p)) = _
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply S T
    (T ⊗[S] FourRootOrder318.Order b), AlgEquiv.commutes]
  all_goals rfl

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
  change (fullOverlap R d a).symm
    (baseChangedOrderMapAlong (reciprocalMap R).toRingHom
      (DVRNormalizedInfinityOrder318.coefficient R d a)
      (algebraMap R[X] (InfinityOrder R d a) p)) = _
  rw [baseChangedOrderMapAlong_scalar, AlgEquiv.commutes]

@[expose] def commonT : (CommonOrder R d a)ˣ :=
  Units.map (algebraMap (Laurent R) (CommonOrder R d a)).toMonoidHom (coordinate R)

theorem finite_evaluation :
    (finiteMap R d a).comp (algebraMap R[X] (FiniteOrder R d a))=
      (Polynomial.aeval (R:=R) (commonT R d a:CommonOrder R d a)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply,finite_polynomial]
    change algebraMap (Laurent R) (CommonOrder R d a)
      (algebraMap R[X] (Laurent R) (C r)) =
      Polynomial.aeval (R:=R) (commonT R d a:CommonOrder R d a) (C r)
    rw [Polynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply R (Laurent R) (CommonOrder R d a) r).symm
  · rw [RingHom.comp_apply,finite_polynomial]
    change algebraMap (Laurent R) (CommonOrder R d a)
      (algebraMap R[X] (Laurent R) X) =
      Polynomial.aeval (R:=R) (commonT R d a:CommonOrder R d a) X
    rw [Polynomial.aeval_X]
    change algebraMap (Laurent R) (CommonOrder R d a) (algebraMap R[X] (Laurent R) X)=
      algebraMap (Laurent R) (CommonOrder R d a) (coordinate R:Laurent R)
    rw [coordinate_value]

theorem infinity_evaluation :
    (infinityMap R d a).comp (algebraMap R[X] (InfinityOrder R d a))=
      (Polynomial.aeval (R:=R) (↑(commonT R d a)⁻¹:CommonOrder R d a)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply,infinity_polynomial]
    change algebraMap (Laurent R) (CommonOrder R d a) (reciprocalMap R (C r)) =
      Polynomial.aeval (R:=R) (↑(commonT R d a)⁻¹:CommonOrder R d a) (C r)
    simp only [reciprocalMap,Polynomial.aeval_C,←IsScalarTower.algebraMap_apply]
  · rw [RingHom.comp_apply,infinity_polynomial]
    change algebraMap (Laurent R) (CommonOrder R d a) (reciprocalMap R X) =
      Polynomial.aeval (R:=R) (↑(commonT R d a)⁻¹:CommonOrder R d a) X
    rw [Polynomial.aeval_X]
    change algebraMap (Laurent R) (CommonOrder R d a) (↑(coordinate R)⁻¹:Laurent R)=_
    exact map_units_inv _ _
end NormalizedWholeScalarMaps318
