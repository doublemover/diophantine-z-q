module
public import PELOriginalCompletedIndependentMap318
public import LegendreNativeInfinityGerm318
public import PELOriginalInfinityBranchExtension318
public section
noncomputable section
namespace PELOriginalCompletedInfinityAtlas318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalRegularCoverPatches318 PELOriginalGluedLegendreMap318
open PELOriginalCompletedLegendreBijection318 LegendreLiteralCompletedAtlas318
open PELOriginalInfinityBranchSource318 LegendrePlaneOverlap318
open PELOriginalCompletedIndependentMap318
variable (i:Fin 4)
local instance : Fact (branchParameter i≠0 ∧ branchParameter i≠1):=
  ⟨branchParameter_nonexceptional i⟩
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (PELOriginalCompletedIndependentMap318.Target i):=
  LegendreCompletedComplexAtlas318.chartedSpace (branchParameter i)
local instance : IsManifold 𝓘(ℂ,ℂ) ω (PELOriginalCompletedIndependentMap318.Target i):=
  LegendreCompletedComplexAtlas318.complex_manifold (branchParameter i)

lemma regular_y_ne_zero (x:CharacterBase i) (hx:x∈Regular i) :
    (coordinates i x).2≠0 := by
  obtain ⟨h0,h1,hl⟩:=PELOriginalGluedLegendreFibers318.finiteMap_regular i ⟨x,hx⟩
  change (coordinates i x).1≠0 at h0
  change (coordinates i x).1≠1 at h1
  change (coordinates i x).1≠branchParameter i at hl
  intro hy
  have he:=coordinates_equation i x hx
  rw [hy,zero_pow (by decide:2≠0)] at he
  exact (mul_ne_zero (mul_ne_zero h0 (sub_ne_zero.mpr h1)) (sub_ne_zero.mpr hl)) he.symm

/-- The infinity extension lies in the ACTUAL independent native chart
on a FULL neighborhood, including its origin, and equals the FIXED
completed map there. Thus no set-theoretic completion is mistaken for
an analytic extension. -/
theorem parameter_holomorphic (p:CharacterBase i)
    (hp:PELOriginalNormalizedDoubleCover318.normalizedMap i p=∞) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun w=>map i (source i p hp w)) 0 := by
  obtain ⟨U,V,k,hU,hV,hU0,hV0,hUd,hk,hk0,hleft,hright,he,hformula,hcenter⟩:=
    PELOriginalInfinityBranchExtension318.infinity_branch i p hp
  let l:=branchParameter i
  let g:=LegendreNativeInfinityGerm318.point l U V
  have ha:AnalyticAt ℂ (fun w=>(g w).val) 0:=
    LegendreNativeInfinityGerm318.analytic l U V hU hV he
  have hpun:∀ᶠ w in 𝓝[≠] (0:ℂ),
      map i (source i p hp w)=infinityChart l (g w):=by
    filter_upwards [source_regular i p hp,hformula,he.filter_mono nhdsWithin_le_nhds]
      with w hw hf hew
    have hy:=regular_y_ne_zero i (source i p hp w) hw
    have hv:(g w).val.2≠0:=by
      rw [LegendreNativeInfinityGerm318.value l U V w hew]
      rw [hf.2]
      exact inv_ne_zero hy
    apply (literalCompletedEquiv l).injective
    change literalCompletedEquiv l ((literalCompletedEquiv l).symm
      (completedMap i (source i p hp w)))=_
    rw [Equiv.apply_symm_apply,completedMap_regular i ⟨source i p hp w,hw⟩,
      LegendreNativeGermHolomorphy318.literal_infinity l (g w) hv]
    apply congrArg some
    apply Subtype.ext
    exact (LegendreNativeInfinityGerm318.literal_value l U V w
      (coordinates i (source i p hp w)).1 (coordinates i (source i p hp w)).2
      hy hew hf.1 hf.2).symm
  have hc:map i (source i p hp 0)=infinityChart l (g 0):=by
    change (literalCompletedEquiv l).symm (completedMap i (source i p hp 0))=_
    rw [hcenter,LegendreNativeGermHolomorphy318.literal_inverse_infinity,
      LegendreNativeInfinityGerm318.center l U V hU0 hV0]
  have hh:=LegendreNativeGermHolomorphy318.infinity l g 0 ha
  apply hh.congr_of_eventuallyEq
  have hn:=eventually_nhdsWithin_iff.mp hpun
  filter_upwards [hn] with w hw
  by_cases hz:w=0
  · simpa only [hz] using hc
  · exact hw hz

/-- The actual inverse source parameter supplies a neighborhood of the
ORIGINAL infinity point. Its forward chart analyticity is derived, not
assumed as a hidden extra branch signature. -/
theorem holomorphic (p:CharacterBase i)
    (hp:PELOriginalNormalizedDoubleCover318.normalizedMap i p=∞) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (map i) p :=
  PELOriginalBranchParameterLocality318.transfer (parameter i p hp) (map i)
    (parameter_holomorphic i p hp)
end PELOriginalCompletedInfinityAtlas318
