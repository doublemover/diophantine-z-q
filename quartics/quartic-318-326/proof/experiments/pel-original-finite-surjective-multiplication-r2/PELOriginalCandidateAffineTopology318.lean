module
public import PELOriginalCandidateHomeomorph318
public section
noncomputable section
namespace PELOriginalCandidateAffineTopology318
open Set QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalCandidateHomeomorph318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateAffineOpenImage318
open PELOriginalClosedAffineImage318 ComplexProjectiveComplexAtlas318
open ComplexProjectiveQuotientTopology318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance targetTopology : TopologicalSpace (PELOriginalAllLevelHolomorphicMap318.Target 1) :=
  topology (Label 3)

/-- Actual inverse ambient affine chart into the FULL independent
projective candidate, with its original ambient subspace topology. -/
@[expose] def projectivePoint (w : Locus τ hτ j) : CandidatePoints τ hτ :=
  ⟨(localChart (Label 3) 0 j).symm w.val,by
    rw [PELOriginalFullCandidatePoints318.projective_equality]
    have hw := (PELOriginalFullAffineCandidateImage318.full_candidate_subset_original τ hτ j) w.property
    rwa [affineImage_eq_preimage] at hw⟩

lemma projectivePoint_continuous : Continuous (projectivePoint τ hτ j) :=
  ((continuousOn_univ.mp (localChart (Label 3) 0 j).continuousOn_invFun).comp
    continuous_subtype_val).subtype_mk _

/-- The inverse sends each full affine candidate point to the original
torus point, continuously and without an auxiliary denominator. -/
@[expose] def sourcePoint (w : Locus τ hτ j) : Base τ :=
  (comparison τ hτ).symm (projectivePoint τ hτ j w)
lemma sourcePoint_continuous : Continuous (sourcePoint τ hτ j) :=
  (comparison τ hτ).symm.continuous.comp (projectivePoint_continuous τ hτ j)
lemma sourcePoint_image (w : Locus τ hτ j) :
    projectiveMap τ hτ 1 (sourcePoint τ hτ j w) =
      (localChart (Label 3) 0 j).symm w.val := inverse_value τ hτ _

/-- The literal original ratio vector has its literal original quotient
point as inverse. This fixes the comparison on the actual covering map. -/
lemma sourcePoint_original (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    sourcePoint τ hτ j ⟨ratioVector τ hτ 1 j z,
      PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ =
        DiscreteComplexPeriodAtlas318.projection (P τ) z := by
  apply PELOriginalLevelThreePointSeparation318.injective τ hτ
  rw [sourcePoint_image,original_covering_square,←actual_ratio]
  exact (localChart (Label 3) 0 j).left_inv
    ((mk_mem_domain (Label 3) j _ _).mpr hz)

lemma sourcePoint_injective : Function.Injective (sourcePoint τ hτ j) := by
  intro w w' h
  apply Subtype.ext
  have he := congrArg (projectiveMap τ hτ 1) h
  rw [sourcePoint_image,sourcePoint_image] at he
  have hc := congrArg (localChart (Label 3) 0 j) he
  simpa only [(localChart (Label 3) 0 j).right_inv (mem_univ w.val),
    (localChart (Label 3) 0 j).right_inv (mem_univ w'.val)] using hc
end PELOriginalCandidateAffineTopology318
