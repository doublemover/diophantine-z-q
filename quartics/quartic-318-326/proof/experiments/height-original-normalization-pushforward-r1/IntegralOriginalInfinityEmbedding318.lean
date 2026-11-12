module
public import IntegralOverlapRootGenerators318
public import IntegralWholeProjectiveProper318
public section
noncomputable section
namespace IntegralOriginalInfinityEmbedding318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalGluing318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

/-- The existing restricted infinity chart enters its actual whole order by
the literal denominator base localization followed by its original order
base-change equivalence. -/
@[expose] def ringMap : InfinityOrder R c →+* IntegralInfinityChart318.Order R c :=
  (infinityLocalization R c).toRingHom.comp
    (Algebra.TensorProduct.includeRight : InfinityOrder R c →ₐ[R[X]]
      IntegralInfinityChart318.Base R c ⊗[R[X]] InfinityOrder R c).toRingHom
@[expose] def inclusion :
    Spec (CommRingCat.of (IntegralInfinityChart318.Order R c)) ⟶ infinityScheme R c :=
  Spec.map (CommRingCat.ofHom (ringMap R c))

instance inclusion_open : IsOpenImmersion (inclusion R c) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra
    R[X] (IntegralInfinityChart318.Base R c) (InfinityOrder R c)
  letI := IntegralInfinityOverlapRealization318.baseChange_localization
    R[X] (IntegralInfinityChart318.Base R c) (InfinityOrder R c)
    (IntegralInfinityChart318.denominator R c)
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : InfinityOrder R c →ₐ[R[X]]
        IntegralInfinityChart318.Base R c ⊗[R[X]] InfinityOrder R c).toRingHom)) :=
    IsOpenImmersion.of_isLocalization
      (algebraMap R[X] (InfinityOrder R c) (IntegralInfinityChart318.denominator R c))
  have h : inclusion R c=
      Spec.map (infinityLocalization R c).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : InfinityOrder R c →ₐ[R[X]]
          IntegralInfinityChart318.Base R c ⊗[R[X]] InfinityOrder R c).toRingHom) := by
    rw [←Spec.map_comp]
    rfl
  rw [h]
  infer_instance

theorem inclusion_range : (inclusion R c).opensRange=
    PrimeSpectrum.basicOpen
      (algebraMap R[X] (InfinityOrder R c) (IntegralInfinityChart318.denominator R c)) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra
    R[X] (IntegralInfinityChart318.Base R c) (InfinityOrder R c)
  letI := IntegralInfinityOverlapRealization318.baseChange_localization
    R[X] (IntegralInfinityChart318.Base R c) (InfinityOrder R c)
    (IntegralInfinityChart318.denominator R c)
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : InfinityOrder R c →ₐ[R[X]]
        IntegralInfinityChart318.Base R c ⊗[R[X]] InfinityOrder R c).toRingHom)) :=
    IsOpenImmersion.of_isLocalization
      (algebraMap R[X] (InfinityOrder R c) (IntegralInfinityChart318.denominator R c))
  have h : inclusion R c=
      Spec.map (infinityLocalization R c).toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : InfinityOrder R c →ₐ[R[X]]
          IntegralInfinityChart318.Base R c ⊗[R[X]] InfinityOrder R c).toRingHom) := by
    rw [←Spec.map_comp]
    rfl
  rw [h,Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (IntegralInfinityChart318.Base R c ⊗[R[X]] InfinityOrder R c)
    (algebraMap R[X] (InfinityOrder R c) (IntegralInfinityChart318.denominator R c))

@[expose] def chart : Spec (CommRingCat.of (IntegralInfinityChart318.Order R c)) ⟶ scheme R c :=
  inclusion R c ≫ infinityChart R c
instance chart_open : IsOpenImmersion (chart R c) := by unfold chart;infer_instance

theorem polynomial (p : R[X]) : ringMap R c (algebraMap R[X] (InfinityOrder R c) p)=
    algebraMap R[X] (IntegralInfinityChart318.Order R c) p := by
  change infinityLocalization R c
    (Algebra.TensorProduct.includeRight (algebraMap R[X] (InfinityOrder R c) p)) = _
  rw [AlgHom.commutes,IsScalarTower.algebraMap_apply R[X] (IntegralInfinityChart318.Base R c)
    (IntegralInfinityChart318.Base R c ⊗[R[X]] InfinityOrder R c),AlgEquiv.commutes,
    ←IsScalarTower.algebraMap_apply]
end IntegralOriginalInfinityEmbedding318
