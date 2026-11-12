module
public import PELOriginalRegularIndependentAtlas318
public import PELOriginalFiniteBranchExtension318
public import LegendreNativeGermHolomorphy318
public import PELOriginalBranchParameterLocality318
public section
noncomputable section
namespace PELOriginalCompletedIndependentMap318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalRegularCoverPatches318 PELOriginalGluedLegendreMap318
open PELOriginalCompletedLegendreBijection318 LegendreLiteralCompletedAtlas318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
abbrev Target := LegendrePlaneOverlap318.CompletedPlane (branchParameter i)

/-- The FIXED completed scheme-point map, now expressed in the actual
independent target complex topology. This is a relabeling of ALL points,
not a new analytic extension selected separately at each branch. -/
@[expose] def map (x:CharacterBase i) : Target i :=
  (literalCompletedEquiv (branchParameter i)).symm (completedMap i x)
@[expose] def equivalence : CharacterBase i≃Target i:=
  (completedEquiv i).trans (literalCompletedEquiv (branchParameter i)).symm
lemma equivalence_value (x:CharacterBase i) : equivalence i x=map i x:=rfl
lemma bijective : Function.Bijective (map i):=(equivalence i).bijective

lemma actual_scheme (x:CharacterBase i) :
    LegendreCompletedPointIdentification318.schemeEquivalence (branchParameter i) (map i x)=
      NormalizedLegendreFieldPoints318.schemeEquiv (branchParameter i) (completedMap i x) := by
  rw [LegendreLiteralCompletedAtlas318.actual_scheme]
  change NormalizedLegendreFieldPoints318.schemeEquiv (branchParameter i)
    (literalCompletedEquiv (branchParameter i)
      ((literalCompletedEquiv (branchParameter i)).symm (completedMap i x)))=_
  rw [Equiv.apply_symm_apply]
lemma actual_projection (x:CharacterBase i) :
    NormalizedLegendreFiniteProjection318.project (branchParameter i)
      (LegendreCompletedPointIdentification318.schemeEquivalence (branchParameter i) (map i x))=
        PELOriginalCommonLegendreBase318.originalProjection i x := by
  rw [actual_scheme]
  exact completed_scheme_projection i x
lemma regular_value (x:CharacterBase i) (hx:x∈Regular i) :
    map i x=PELOriginalRegularIndependentAtlas318.comparison i x := by
  unfold map
  rw [completedMap_regular i ⟨x,hx⟩,LegendreNativeGermHolomorphy318.literal_inverse_finite,
    PELOriginalRegularIndependentAtlas318.comparison_finite i ⟨x,hx⟩]

local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (Target i):=
  LegendreCompletedComplexAtlas318.chartedSpace (branchParameter i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Target i):=
  LegendreCompletedComplexAtlas318.complex_manifold (branchParameter i)

/-- The same completed map is holomorphic on the whole original regular
locus; this is actual equality on an open neighborhood, not pointwise
substitution into a holomorphy theorem. -/
theorem regular_holomorphic (x:CharacterBase i) (hx:x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (map i) x := by
  apply (PELOriginalRegularIndependentAtlas318.holomorphic i x hx).congr_of_eventuallyEq
  filter_upwards [(regular_open i).mem_nhds hx] with y hy
  exact regular_value i y hy

/-- Across each ACTUAL finite branch, the fixed completed map pulled
back by the original square parameter is holomorphic in the independent
completed target atlas, with continuity a conclusion. -/
theorem finite_branch_parameter_holomorphic (j:Fin 3) (p:CharacterBase i)
    (hp:PELOriginalNormalizedDoubleCover318.normalizedMap i p=
      (LegendreSimpleBranchCharts318.branch (branchParameter i) j:OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun w=>map i (PELOriginalFiniteBranchSource318.source i j p hp w)) 0 := by
  obtain ⟨q,k,hq,hq0,hqd,hk,hk0,hl,hr,hqs,hA,hpoint⟩:=
    PELOriginalFiniteBranchExtension318.finite_branch i j p hp
  let g:=fun w=>LegendreLiteralFiniteBranch318.point (branchParameter i)
    (branchParameter_nonexceptional i).1 (branchParameter_nonexceptional i).2 j (q w)
  have hh:=LegendreNativeGermHolomorphy318.literal_finite (branchParameter i) g 0 hA
  apply hh.congr_of_eventuallyEq
  filter_upwards [hpoint] with w hw
  change (literalCompletedEquiv (branchParameter i)).symm
    (completedMap i (PELOriginalFiniteBranchSource318.source i j p hp w))=
      (literalCompletedEquiv (branchParameter i)).symm (some (g w))
  exact congrArg (literalCompletedEquiv (branchParameter i)).symm hw
/-- The actual source inverse coordinate transfers the finite-branch
formula to EVERY nearby original point, in the ORIGINAL source atlas. -/
theorem finite_branch_holomorphic (j:Fin 3) (p:CharacterBase i)
    (hp:PELOriginalNormalizedDoubleCover318.normalizedMap i p=
      (LegendreSimpleBranchCharts318.branch (branchParameter i) j:OnePoint ℂ)) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (map i) p :=
  PELOriginalBranchParameterLocality318.transfer
    (PELOriginalFiniteBranchSource318.parameter i j p hp) (map i)
    (finite_branch_parameter_holomorphic i j p hp)
end PELOriginalCompletedIndependentMap318
