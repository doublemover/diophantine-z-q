module
public import FifthCompletedDegree318
public import FifthTargetParameterRestriction318
public import SchematicEqualityExtension318
public import ProperFiniteFiberDescent318
public section
noncomputable section
namespace FifthReciprocalBaseSquare318
open AlgebraicGeometry CategoryTheory Polynomial SourceTwistArithmetic318
open FifthCharacterShortPolynomial318
set_option maxHeartbeats 120000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma reciprocal_ring_square:
    (Polynomial.aeval FifthSourceInfinityCoordinates318.u).toRingHom=
      (ReciprocalInfinityBase318.chartMap units).comp
        (algebraMap ℚ[X] (ReciprocalInfinityBase318.ReciprocalOpen units)):=by
  apply Polynomial.ringHom_ext
  · intro q
    simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C]
    change algebraMap ℚ _ q=(ReciprocalInfinityBase318.chartMap units)
      (algebraMap ℚ[X] (ReciprocalInfinityBase318.ReciprocalOpen units) (C q))
    have hc:algebraMap ℚ[X] (ReciprocalInfinityBase318.ReciprocalOpen units) (C q)=
        algebraMap ℚ (ReciprocalInfinityBase318.ReciprocalOpen units) q:=
      (IsScalarTower.algebraMap_apply ℚ ℚ[X] (ReciprocalInfinityBase318.ReciprocalOpen units) q).symm
    rw [hc,RingHom.map_rat_algebraMap]
  · simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X]
    apply InfinityOpenFractionField318.openEmbedding_injective units
    change InfinityOpenFractionField318.openEmbedding units FifthSourceInfinityCoordinates318.u=
      ReciprocalInfinityNormalization318.reciprocalEmbedding units
        (algebraMap ℚ[X] (ReciprocalInfinityBase318.ReciprocalOpen units) X)
    rw [ReciprocalInfinityNormalization318.reciprocalEmbedding_coordinate]
    exact FifthSourceInfinityCoordinates318.u_embedding

end FifthReciprocalBaseSquare318
