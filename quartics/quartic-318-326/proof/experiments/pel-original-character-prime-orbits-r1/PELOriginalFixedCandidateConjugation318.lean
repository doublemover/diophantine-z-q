module
public import PELFixedCandidateCoverage318
public section
noncomputable section
namespace PELOriginalFixedCandidateConjugation318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318
open PELLevelThreeSimilitudes318 PELIntegralEllipticObstructions318
open PELOriginalFixedIntegralCoordinates318 PELOriginalFixedPolygonSearch318
open PELFixedCandidateCoverage318 PELFixedCandidateConjugators318
open PELPositiveOrderNormalizer318 QuaternionicFixedParameter318
open QuaternionicJointPeriodTopology318 PELQuaternionRealRepresentation318
open PELDirichletHeight318 PELJointNormOneAction318

/-- Every original integral trace-zero fixed normalizer in an ACTUAL
original-group height-minimizing representative is conjugate to its original
labeled inertia. Finite-list membership and the positive normalizer are
both constructed, not additional caller assumptions. -/
theorem original_minimum_conjugate (x : Coordinates) (ht : trace x=0)
    (i : Fin 5) (hn : integralNorm x=(PELFixedNormalizerFiniteSearch318.norm i:ℤ))
    (hr : 0<rotationCoordinate x) (τ : HalfPlane)
    (hfix : fixesLine (representation (embed x)) τ)
    (hmin : ∀ u : normOneUnits,height τ≤height (u • τ)) :
    ∃ g : positiveNormalizer,
      (g.val:B)*PELInertiaNormalizerData318.element i*((g.val⁻¹:Bˣ):B)=embed x := by
  have hs := original_finite_list x ht i hn hr τ hfix hmin
  obtain ⟨k,hki,hkx⟩ := original_candidate_covered i x ht hr hs
  refine ⟨conjugator k,?_⟩
  simpa only [hki,hkx] using actual_conjugation k
end PELOriginalFixedCandidateConjugation318
