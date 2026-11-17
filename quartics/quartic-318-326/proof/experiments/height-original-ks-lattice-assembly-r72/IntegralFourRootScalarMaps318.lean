module
public import IntegralFourRootGluing318
public import JLineOverlap318
public section
noncomputable section
namespace IntegralFourRootScalarMaps318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralFourRootReciprocalCharts318 IntegralFourRootOverlap318 FourRootOrderOpenMaps318
open IntegralWholeReciprocalOverlap318 (Laurent y y_value)
open scoped TensorProduct
universe u
private lemma baseChanged_scalar {A T : Type u} [CommRing A] [CommRing T]
    [Algebra A T] (b : Fin 4 → A) (p : A) :
    baseChangedOrderMap (T:=T) b (algebraMap A (FourRootOrder318.Order b) p) =
      algebraMap T (FourRootOrder318.Order (fun i => algebraMap A T (b i)))
        (algebraMap A T p) := by
  change FourRootOrder318.baseChange b T
    (Algebra.TensorProduct.includeRight (algebraMap A (FourRootOrder318.Order b) p)) = _
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply A T
    (T ⊗[A] FourRootOrder318.Order b),AlgEquiv.commutes]

variable (R : Type*) [CommRing R] (d a : Fin 4 → R)

theorem finite_polynomial (p : R[X]) :
    finiteMap R d a (algebraMap R[X] (FiniteOrder d a) p) =
      algebraMap (Laurent R) (CommonOrder R d a) (algebraMap R[X] (Laurent R) p) :=
  baseChanged_scalar (finiteCoefficient d a) p

theorem infinity_polynomial (p : R[X]) :
    infinityMap R d a (algebraMap R[X] (ReciprocalOrder d a) p) =
      algebraMap (Laurent R) (CommonOrder R d a) (reciprocalMap R p) := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R).toRingHom.toAlgebra
  change (fullOverlap R d a)
    (baseChangedOrderMap (T:=Laurent R) (reciprocalCoefficient d a)
      (algebraMap R[X] (ReciprocalOrder d a) p)) = _
  rw [baseChanged_scalar]
  exact (fullOverlap R d a).commutes (reciprocalMap R p)

@[expose] def commonY : (CommonOrder R d a)ˣ :=
  Units.map (algebraMap (Laurent R) (CommonOrder R d a)).toMonoidHom (y R)

theorem finite_evaluation :
    (finiteMap R d a).comp (algebraMap R[X] (FiniteOrder d a)) =
      (Polynomial.aeval (R:=R) (commonY R d a : CommonOrder R d a)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change finiteMap R d a (algebraMap R[X] (FiniteOrder d a) (C r)) =
      Polynomial.aeval (R:=R) (commonY R d a : CommonOrder R d a) (C r)
    rw [finite_polynomial,Polynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply R (Laurent R) (CommonOrder R d a) r).symm
  · change finiteMap R d a (algebraMap R[X] (FiniteOrder d a) X) =
      Polynomial.aeval (R:=R) (commonY R d a : CommonOrder R d a) X
    rw [finite_polynomial,Polynomial.aeval_X]
    change algebraMap (Laurent R) (CommonOrder R d a) (algebraMap R[X] (Laurent R) X) =
      algebraMap (Laurent R) (CommonOrder R d a) (y R : Laurent R)
    rw [y_value]

theorem infinity_evaluation :
    (infinityMap R d a).comp (algebraMap R[X] (ReciprocalOrder d a)) =
      (Polynomial.aeval (R:=R) (((commonY R d a)⁻¹ : (CommonOrder R d a)ˣ) : CommonOrder R d a)).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change infinityMap R d a (algebraMap R[X] (ReciprocalOrder d a) (C r)) =
      Polynomial.aeval (R:=R) (((commonY R d a)⁻¹ : (CommonOrder R d a)ˣ) : CommonOrder R d a) (C r)
    rw [infinity_polynomial,reciprocalMap_eval,Polynomial.aeval_C,Polynomial.aeval_C]
    exact (IsScalarTower.algebraMap_apply R (Laurent R) (CommonOrder R d a) r).symm
  · change infinityMap R d a (algebraMap R[X] (ReciprocalOrder d a) X) =
      Polynomial.aeval (R:=R) (((commonY R d a)⁻¹ : (CommonOrder R d a)ˣ) : CommonOrder R d a) X
    rw [infinity_polynomial,reciprocalMap_eval,Polynomial.aeval_X,Polynomial.aeval_X]
    rfl

end IntegralFourRootScalarMaps318
