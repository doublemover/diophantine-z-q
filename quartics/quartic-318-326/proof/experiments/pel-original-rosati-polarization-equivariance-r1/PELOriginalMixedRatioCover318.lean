module
public import PELOriginalProjectiveRatioInputs318
public import ProjectiveSubopenRatioAtlas318
public section
noncomputable section
namespace PELOriginalMixedRatioCover318
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PELOriginalLevelTheta318 PELOriginalReducedProjectiveCandidate318
open PELOriginalProjectiveRatioInputs318 ProjectivePreimageRegularRatios318
variable (τ : ℂ) (hτ : 0 < τ.im)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ
local instance candidateIntegral : IsIntegral (candidate τ hτ) := PELOriginalCandidateIntegral318.integral τ hτ

abbrev Index := Label 3 × Label 2
/-- Genuine common refinement of the cubic and quadratic standard-open
preimages. Every member is an open of the SAME whole candidate. -/
abbrev mixedOpen (a : Index) : (candidate τ hτ).Opens := cubicOpen τ hτ a.1 ⊓ quadraticOpen τ hτ a.2

/-- All scheme primes, not only closed points, lie on some mixed chart. -/
theorem covers (x : candidate τ hτ) : ∃ a : Index, x ∈ mixedOpen τ hτ a := by
  obtain ⟨j,hj⟩ := source_cover (inclusion τ hτ) x
  obtain ⟨s,hs⟩ := source_cover (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ) x
  exact ⟨(j,s),hj,hs⟩

/-- A real common rational anchor exists; no simultaneous nonvanishing
of arbitrarily prescribed theta coordinates is assumed. -/
theorem exists_anchor : ∃ a : Index, Nonempty (mixedOpen τ hτ a) := by
  let x : candidate τ hτ := Classical.choice inferInstance
  obtain ⟨a,ha⟩ := covers τ hτ x
  exact ⟨a,⟨⟨x,ha⟩⟩⟩

/-- Discarding empty mixed opens still covers every scheme prime. This
indexing supplies exactly the nonempty integral charts needed by the
rational-image line-sheaf construction. -/
abbrev NonemptyIndex := {a : Index // Nonempty (mixedOpen τ hτ a)}
theorem nonempty_covers (x : candidate τ hτ) :
    ∃ a : NonemptyIndex τ hτ, x ∈ mixedOpen τ hτ a.1 := by
  obtain ⟨a,ha⟩ := covers τ hτ x
  exact ⟨⟨a,⟨⟨x,ha⟩⟩⟩,ha⟩

/-- Any two actual nonempty mixed charts meet, by the proved integral
candidate topology, including charts meeting the old denominator boundary. -/
theorem intersection_nonempty (a b : NonemptyIndex τ hτ) :
    Nonempty (mixedOpen τ hτ a.1 ⊓ mixedOpen τ hτ b.1) := by
  obtain ⟨x,hx⟩ := nonempty_preirreducible_inter
    (mixedOpen τ hτ a.1).isOpen (mixedOpen τ hτ b.1).isOpen
    (by obtain ⟨x⟩ := a.2; exact ⟨x,x.property⟩)
    (by obtain ⟨x⟩ := b.2; exact ⟨x,x.property⟩)
  exact ⟨⟨x,hx⟩⟩

@[expose] def cubic (a : Index) (i : Label 3) : Γ((mixedOpen τ hτ a).toScheme,⊤) :=
  ProjectiveSubopenRatioAtlas318.ratio (inclusion τ hτ) _ a.1 inf_le_left i
@[expose] def quadratic (a : Index) (i : Label 2) : Γ((mixedOpen τ hτ a).toScheme,⊤) :=
  ProjectiveSubopenRatioAtlas318.ratio (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ)
    _ a.2 inf_le_right i
lemma cubic_self (a : Index) : cubic τ hτ a a.1=1 :=
  ProjectiveSubopenRatioAtlas318.ratio_self _ _ _ _
lemma quadratic_self (a : Index) : quadratic τ hτ a a.2=1 :=
  ProjectiveSubopenRatioAtlas318.ratio_self _ _ _ _

abbrev overlap (a b : Index) := mixedOpen τ hτ a ⊓ mixedOpen τ hτ b
@[expose] def toLeft (a b : Index) : (overlap τ hτ a b).toScheme ⟶ (mixedOpen τ hτ a).toScheme :=
  (candidate τ hτ).homOfLE inf_le_left
@[expose] def toRight (a b : Index) : (overlap τ hτ a b).toScheme ⟶ (mixedOpen τ hτ b).toScheme :=
  (candidate τ hτ).homOfLE inf_le_right

/-- Actual linear cubic coefficient equation on the whole mixed overlap. -/
theorem cubic_transition (a b : Index) (i : Label 3) :
    (toLeft τ hτ a b).appTop (cubic τ hτ a i) =
      (toRight τ hτ a b).appTop (cubic τ hτ b i) *
        (toLeft τ hτ a b).appTop (cubic τ hτ a b.1) := by
  simpa only [cubic,toLeft,toRight,ProjectiveSubopenRatioAtlas318.ratio_restrict] using
    ProjectiveSubopenRatioAtlas318.transition (inclusion τ hτ)
      (PELOriginalProperComplexCandidate318.structureMap τ hτ)
      (PELOriginalProperComplexCandidate318.inclusion_over τ hτ) (cubic_point_model τ hτ)
      (overlap τ hτ a b) a.1 b.1 i (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)

theorem quadratic_transition (a b : Index) (i : Label 2) :
    (toLeft τ hτ a b).appTop (quadratic τ hτ a i) =
      (toRight τ hτ a b).appTop (quadratic τ hτ b i) *
        (toLeft τ hτ a b).appTop (quadratic τ hτ a b.2) := by
  simpa only [quadratic,toLeft,toRight,ProjectiveSubopenRatioAtlas318.ratio_restrict] using
    ProjectiveSubopenRatioAtlas318.transition (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ)
      (PELOriginalProperComplexCandidate318.structureMap τ hτ)
      (PELOriginalLevelTwoSchemeMorphism318.over_complex τ hτ) (quadratic_point_model τ hτ)
      (overlap τ hτ a b) a.2 b.2 i (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)

theorem cubic_unit (a b : Index) : IsUnit ((toLeft τ hτ a b).appTop (cubic τ hτ a b.1)) := by
  simpa only [cubic,toLeft,ProjectiveSubopenRatioAtlas318.ratio_restrict] using
    ProjectiveSubopenRatioAtlas318.transition_isUnit (inclusion τ hτ)
      (PELOriginalProperComplexCandidate318.structureMap τ hτ)
      (PELOriginalProperComplexCandidate318.inclusion_over τ hτ) (cubic_point_model τ hτ)
      (overlap τ hτ a b) a.1 b.1 (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)

theorem quadratic_unit (a b : Index) : IsUnit ((toLeft τ hτ a b).appTop (quadratic τ hτ a b.2)) := by
  simpa only [quadratic,toLeft,ProjectiveSubopenRatioAtlas318.ratio_restrict] using
    ProjectiveSubopenRatioAtlas318.transition_isUnit (PELOriginalLevelTwoSchemeMorphism318.morphism τ hτ)
      (PELOriginalProperComplexCandidate318.structureMap τ hτ)
      (PELOriginalLevelTwoSchemeMorphism318.over_complex τ hτ) (quadratic_point_model τ hτ)
      (overlap τ hτ a b) a.2 b.2 (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
end PELOriginalMixedRatioCover318
