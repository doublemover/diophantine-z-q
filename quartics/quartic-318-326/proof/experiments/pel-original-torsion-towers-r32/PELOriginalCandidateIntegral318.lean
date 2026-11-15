module
public import PELOriginalCandidateChartSections318
public import PELOriginalSectionRingDomain318
public import Mathlib.Topology.Irreducible
public section
noncomputable section
namespace PELOriginalCandidateIntegral318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PELOriginalReducedProjectiveCandidate318 PELOriginalCubicRelationIdeal318
open PELOriginalProjectiveCandidatePoints318 PELOriginalPolarizationTransitions318
variable (τ:ℂ)(hτ:0<τ.im)
local instance standardGrading:GradedAlgebra degrees:=MvPolynomial.gradedAlgebra

/-- The generic projective point is the LITERAL original relation prime.
Relevance follows from an actual nonzero original cubic coordinate, not
from an asserted dimension or analytic/algebraic image theorem. -/
@[expose] def genericPoint:ambient where
  asHomogeneousIdeal:=⟨relations τ hτ,relations_homogeneous τ hτ⟩
  isPrime:=PELOriginalSectionRingDomain318.relationsPrime τ hτ
  not_irrelevant_le:=by
    let q:Base τ:=Classical.choice inferInstance
    intro h
    exact (originalPoint τ hτ q).not_irrelevant_le
      (fun p hp=>relations_contained τ hτ q (h hp))

lemma zeroSet_generic:
    (zeroSet τ hτ:Set ambient)=closure ({genericPoint τ hτ}:Set ambient):=by
  ext p
  change (genericPoint τ hτ≤p)↔p∈closure ({genericPoint τ hτ}:Set ambient)
  exact ProjectiveSpectrum.le_iff_mem_closure _ _
lemma zeroSet_irreducible:IsIrreducible (zeroSet τ hτ:Set ambient):=by
  rw [zeroSet_generic]
  exact isIrreducible_singleton.closure

/-- Irreducibility transfers through the ACTUAL closed-immersion image
homeomorphism. No complex-point surjectivity or Chow result is used. -/
theorem irreducible:IrreducibleSpace (candidate τ hτ):=by
  have hr:IsIrreducible (Set.range (inclusion τ hτ)):=by
    rw [inclusion_range]
    exact zeroSet_irreducible τ hτ
  haveI:IrreducibleSpace (Set.range (inclusion τ hτ)):=
    isIrreducible_iff_irreducibleSpace.mp hr
  exact ((inclusion τ hτ).isClosedEmbedding.isEmbedding.toHomeomorph.irreducibleSpace_iff).mpr
    inferInstance

theorem integral:IsIntegral (candidate τ hτ):=by
  haveI:IrreducibleSpace (candidate τ hτ):=irreducible τ hτ
  haveI:IsReduced (candidate τ hτ):=reduced τ hτ
  exact isIntegral_of_irreducibleSpace_of_isReduced _
end PELOriginalCandidateIntegral318
