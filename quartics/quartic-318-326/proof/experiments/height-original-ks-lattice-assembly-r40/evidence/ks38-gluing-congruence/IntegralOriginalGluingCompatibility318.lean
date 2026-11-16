module
public import IntegralWholeOverlapGenerators318
public section
noncomputable section
namespace IntegralOriginalGluingCompatibility318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318 IntegralWholeOrderOpenMaps318
open IntegralOriginalCommonRestriction318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Evaluate the original reciprocal unit through an algebra hom before
specializing its concrete localization/tensor dictionaries. -/
private theorem reciprocal_unit_image {k A B : Type*} [CommSemiring k] [Semiring A] [Semiring B]
    [Algebra k A] [Algebra k B] (f : A →ₐ[k] B) (c : kˣ) (u : Aˣ) :
    algebraMap k B (c : k) * (↑(Units.map f.toMonoidHom u)⁻¹ : B) =
      f (↑(Units.map (algebraMap k A).toMonoidHom c * u⁻¹) : A) := by
  change algebraMap k B (c : k) * f (↑u⁻¹ : A) =
    f (algebraMap k A (c : k) * (↑u⁻¹ : A))
  rw [map_mul, f.commutes]

/-- Expand the scalar action through the exact ring map on abstract algebra
carriers before specializing the Laurent and tensor dictionaries. -/
private theorem ring_map_smul {k A B : Type*} [CommSemiring k] [Semiring A] [Semiring B]
    [Algebra k A] (f : A →+* B) (r : k) (a : A) :
    f (r • a) = f (algebraMap k A r) * f a := by
  rw [Algebra.smul_def, map_mul]

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem common_inverse : commonRestriction R c
    (↑(IntegralWholeOrderScalarMaps318.commonY R c)⁻¹:CommonOrder R c)=
      (↑(oldY R c)⁻¹:OldOverlap R c) := by
  have h : Units.map (commonRestriction R c).toMonoidHom
      (IntegralWholeOrderScalarMaps318.commonY R c)=oldY R c :=
    Units.ext (common_y R c)
  exact congrArg (fun z : (OldOverlap R c)ˣ => (↑z⁻¹:OldOverlap R c)) h

theorem common_u : commonRestriction R c
    (algebraMap (Laurent R) (CommonOrder R c) (u R c))=
      IntegralOverlapChartMaps318.commonMap R c
        (IntegralInfinityCommonBase318.reciprocalUnit R c) := by
  rw [u,map_mul,map_mul]
  change commonRestriction R c (algebraMap R (CommonOrder R c) (c 0:R)) *
    commonRestriction R c (↑(IntegralWholeOrderScalarMaps318.commonY R c)⁻¹:CommonOrder R c)=_
  rw [common_constant,common_inverse]
  exact reciprocal_unit_image (IntegralOverlapChartMaps318.commonMap R c)
    (c 0) (IntegralInfinityCommonBase318.rootUnit R c)

/-- Equality of the actual two whole-infinity restriction ring maps, on the
whole polynomial coefficient ring and all three original signed ratio roots. -/
theorem infinity_square :
    (commonRestriction R c).comp (infinityMap R c)=
      (IntegralOverlapChartMaps318.infinityMap R c).toRingHom.comp
        (IntegralOriginalInfinityEmbedding318.ringMap R c) := by
  refine ThreeRootCoordinates318.ringHom_ext (R := R[X]) (U := OldOverlap R c)
    (IntegralInfinityChart318.coefficient R c)
    (f := (commonRestriction R c).comp (infinityMap R c))
    (g := (IntegralOverlapChartMaps318.infinityMap R c).toRingHom.comp
      (IntegralOriginalInfinityEmbedding318.ringMap R c)) ?_ ?_
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply]
      change commonRestriction R c (infinityMap R c
        (algebraMap R[X] (InfinityOrder R c) (C r))) = _
      rw [IntegralWholeOrderScalarMaps318.infinity_polynomial,
        reciprocalMap, Polynomial.aeval_C,
        ← IsScalarTower.algebraMap_apply R (Laurent R) (CommonOrder R c)]
      rw [common_constant,IntegralOriginalInfinityEmbedding318.polynomial]
      exact ((IntegralOverlapChartMaps318.infinityMap R c).commutes r).symm
    · simp only [RingHom.comp_apply]
      change commonRestriction R c (infinityMap R c
        (algebraMap R[X] (InfinityOrder R c) X)) = _
      rw [IntegralWholeOrderScalarMaps318.infinity_polynomial,
        reciprocalMap, Polynomial.aeval_X]
      rw [common_u,IntegralOriginalInfinityEmbedding318.polynomial]
      exact (IntegralOverlapChartMaps318.infinity_coordinate R c).symm
  · intro j
    simp only [RingHom.comp_apply]
    change commonRestriction R c (infinityMap R c (ThreeRootCoordinates318.generator _ j))=_
    conv_lhs => rw [IntegralWholeOverlapGenerators318.infinity_generator R c j]
    conv_rhs =>
      rw [IntegralWholeGeneratorComparisons318.infinity_generator R c j]
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      rw [IntegralOverlapRootGenerators318.infinityMap_generator R c j]
    with_reducible_and_instances
      rw [ring_map_smul (k := Laurent R) (A := CommonOrder R c) (B := OldOverlap R c)
        (commonRestriction R c) (↑(y R)⁻¹ : Laurent R)
        (ThreeRootCoordinates318.generator (finiteParameter R c) j)]
    change commonRestriction R c
      (↑(IntegralWholeOrderScalarMaps318.commonY R c)⁻¹:CommonOrder R c) *
        commonRestriction R c (ThreeRootCoordinates318.generator (finiteParameter R c) j)=_
    have hgen :=
      (congrArg (commonRestriction R c)
        (IntegralWholeOverlapGenerators318.finite_generator R c j).symm).trans
        ((common_finite R c
          (ThreeRootCoordinates318.generator (finiteCoefficient R c) j)).trans
          (finiteRestriction_generator R c j))
    refine (congrArg₂ (fun a b : OldOverlap R c => a * b)
      (common_inverse R c) hgen).trans ?_
    change algebraMap (IntegralInfinityCommonBase318.CommonBase R c) (OldOverlap R c)
      (↑(IntegralInfinityCommonBase318.rootUnit R c)⁻¹) * _ = _
    exact (Algebra.smul_def _ _).symm

@[expose] def intoWholeCommon : IntegralGluedModel318.commonScheme R c ⟶
    IntegralWholeReciprocalGluing318.overlap R c :=
  Spec.map (CommRingCat.ofHom (commonRestriction R c))

theorem finite_square :
    intoWholeCommon R c ≫ IntegralWholeReciprocalGluing318.intoFinite R c =
      IntegralGluedModel318.intoFinite R c ≫
        Spec.map (IntegralWholeFiniteComparison318.comparison R c).symm.toRingEquiv.toCommRingCatIso.hom := by
  unfold intoWholeCommon IntegralWholeReciprocalGluing318.intoFinite IntegralGluedModel318.intoFinite
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact common_finite R c a

theorem reciprocal_square :
    intoWholeCommon R c ≫ IntegralWholeReciprocalGluing318.intoInfinity R c =
      IntegralGluedModel318.intoInfinity R c ≫ IntegralOriginalInfinityEmbedding318.inclusion R c := by
  unfold intoWholeCommon IntegralWholeReciprocalGluing318.intoInfinity
    IntegralGluedModel318.intoInfinity IntegralOriginalInfinityEmbedding318.inclusion
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (infinity_square R c)

/-- The original old-model gluing maps agree inside the proper whole model.
Both sides retain the original source and infinity embeddings. -/
theorem chart_agreement :
    IntegralGluedModel318.intoFinite R c ≫ IntegralWholeReciprocalGluing318.originalSourceChart R c =
      IntegralGluedModel318.intoInfinity R c ≫ IntegralOriginalInfinityEmbedding318.chart R c := by
  change IntegralGluedModel318.intoFinite R c ≫
    (Spec.map (IntegralWholeFiniteComparison318.comparison R c).symm.toRingEquiv.toCommRingCatIso.hom ≫
      IntegralWholeReciprocalGluing318.finiteChart R c) = _
  rw [←Category.assoc,←finite_square,Category.assoc]
  rw [show IntegralWholeReciprocalGluing318.intoFinite R c ≫
      IntegralWholeReciprocalGluing318.finiteChart R c =
      IntegralWholeReciprocalGluing318.intoInfinity R c ≫
        IntegralWholeReciprocalGluing318.infinityChart R c from CategoryTheory.Limits.pushout.condition]
  rw [←Category.assoc,reciprocal_square,Category.assoc]
  rfl
end IntegralOriginalGluingCompatibility318
