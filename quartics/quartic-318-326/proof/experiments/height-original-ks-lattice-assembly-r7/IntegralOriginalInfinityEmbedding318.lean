module
public import IntegralOverlapRootGenerators318
public import IntegralWholeProjectiveProper318
public section
noncomputable section
universe u
namespace IntegralOriginalInfinityEmbedding318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalGluing318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Abstract the native localization proof before specializing its nested
original chart carriers. The resulting ring map is unchanged. -/
private theorem localization_equiv_open
    (P F A B : Type u) [CommRing P] [CommRing F] [CommRing A] [CommRing B]
    [Algebra P F] [Algebra P A] (x : P) [IsLocalization.Away x F]
    (e : F ⊗[P] A ≃+* B) : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom))) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra P F A
  letI := IntegralInfinityOverlapRealization318.baseChange_localization P F A x
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap P A x)
  have h : Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom)) =
      Spec.map e.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom) := by
    rw [←Spec.map_comp]
    rfl
  rw [h]
  infer_instance

private theorem localization_equiv_range
    (P F A B : Type u) [CommRing P] [CommRing F] [CommRing A] [CommRing B]
    [Algebra P F] [Algebra P A] (x : P) [IsLocalization.Away x F]
    (e : F ⊗[P] A ≃+* B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom)))] :
    (Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom))).opensRange =
      PrimeSpectrum.basicOpen (algebraMap P A x) := by
  letI := IntegralInfinityOverlapRealization318.rightAlgebra P F A
  letI := IntegralInfinityOverlapRealization318.baseChange_localization P F A x
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (algebraMap P A x)
  have h : Spec.map (CommRingCat.ofHom
      (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom)) =
      Spec.map e.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom) := by
    rw [←Spec.map_comp]
    rfl
  -- Forget the proof-dependent open-range wrapper before rewriting the map.
  apply TopologicalSpace.Opens.ext
  change Set.range (Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom))) = _
  rw [h]
  have hr := congrArg (fun U : (Spec (CommRingCat.of A)).Opens => (U : Set _))
    (Scheme.Hom.opensRange_comp_of_isIso (Spec.map e.toCommRingCatIso.hom)
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[P] F ⊗[P] A).toRingHom)))
  exact hr.trans
    (PrimeSpectrum.localization_away_comap_range (F ⊗[P] A) (algebraMap P A x))

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
  exact localization_equiv_open R[X] (IntegralInfinityChart318.Base R c)
    (InfinityOrder R c) (IntegralInfinityChart318.Order R c)
    (IntegralInfinityChart318.denominator R c) (infinityLocalization R c).toRingEquiv

theorem inclusion_range : (inclusion R c).opensRange=
    PrimeSpectrum.basicOpen
      (algebraMap R[X] (InfinityOrder R c) (IntegralInfinityChart318.denominator R c)) := by
  -- Supply the helper's exact composite instance rather than asking search
  -- to unfold the public inclusion and the algebra-equivalence coercions.
  letI := localization_equiv_open R[X] (IntegralInfinityChart318.Base R c)
    (InfinityOrder R c) (IntegralInfinityChart318.Order R c)
    (IntegralInfinityChart318.denominator R c) (infinityLocalization R c).toRingEquiv
  exact localization_equiv_range R[X] (IntegralInfinityChart318.Base R c)
    (InfinityOrder R c) (IntegralInfinityChart318.Order R c)
    (IntegralInfinityChart318.denominator R c) (infinityLocalization R c).toRingEquiv

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
