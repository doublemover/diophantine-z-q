module
public import PELOriginalFullCandidateSchemePoints318
public section
noncomputable section
namespace PELOriginalCandidateHomeomorph318
open Set QuaternionicRealPeriod318 PELOriginalLevelTheta318
open DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open ComplexProjectiveQuotientTopology318 PELOriginalProjectiveImageFromAffine318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance targetTopology : TopologicalSpace (PELOriginalAllLevelHolomorphicMap318.Target 1) :=
  topology (Label 3)

/-- The independently topologized FULL projective relation locus.
Its topology is inherited from the original ambient projective space,
not transported from the source torus. -/
abbrev CandidatePoints := projectiveLocus τ hτ

/-- Actual original torus to the FULL independent candidate, through
the genuine closed theta embedding and proved whole-locus equality. -/
@[expose] def comparison : Base τ ≃ₜ CandidatePoints τ hτ :=
  (PELOriginalLevelThreeClosedEmbedding318.imageHomeomorph τ hτ).trans
    (Homeomorph.setCongr (PELOriginalFullCandidatePoints318.projective_equality τ hτ).symm)

@[simp] lemma comparison_value (q : Base τ) :
    (comparison τ hτ q).val = projectiveMap τ hτ 1 q := rfl

lemma inverse_value (p : CandidatePoints τ hτ) :
    projectiveMap τ hτ 1 ((comparison τ hτ).symm p) = p.val := by
  have h := congrArg Subtype.val ((comparison τ hτ).apply_symm_apply p)
  exact h

lemma candidate_closed : IsClosed (projectiveLocus τ hτ) := by
  rw [PELOriginalFullCandidatePoints318.projective_equality]
  exact PELOriginalLevelThreeClosedEmbedding318.image_closed τ hτ

lemma candidate_compact : IsCompact (projectiveLocus τ hτ) := by
  rw [PELOriginalFullCandidatePoints318.projective_equality]
  exact PELOriginalLevelThreeClosedEmbedding318.image_compact τ hτ

/-- Exact forward and inverse on the original quotient-covering map;
no alternate torus or abstract point bijection is substituted. -/
lemma comparison_cover (z : ComplexVectors) :
    (comparison τ hτ (DiscreteComplexPeriodAtlas318.projection
      (P τ) z)).val = coveringMap τ hτ 1 z :=
  original_covering_square τ hτ 1 z
end PELOriginalCandidateHomeomorph318
