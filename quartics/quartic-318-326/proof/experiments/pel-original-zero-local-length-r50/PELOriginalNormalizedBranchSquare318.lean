module
public import PELOriginalAnalyticRealStrip318
public import PELOriginalCharacterLocalSquare318
public import ComplexCurvePartialInverse318
public section
noncomputable section
namespace PELOriginalNormalizedBranchSquare318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalCharacterTopology318 PELOriginalBranchLabels318
open PELOriginalFourBranchCoordinate318 PELOriginalCharacterBranches318
open PELOriginalCharacterTopologicalAtlas318 PELOriginalCharacterComplexAtlas318
open ComplexSphereCharts318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=character_manifold i
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold
local instance : ChartedSpace ℂ PELOriginalMaximalQuotient318.MaximalBase:=
  PELMaximalTopologicalAtlas318.maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω PELOriginalMaximalQuotient318.MaximalBase:=
  PELMaximalComplexAtlas318.maximal_manifold

/-- Genuine original source and normalized BASE coordinates at EVERY
actual branch point, including infinity. The base coordinate is explicitly
the old maximal chart after the inverse of the SAME normalized sphere map.
Both directions are holomorphic in the original atlases. -/
theorem branch_square (q:CharacterBase i)
    (hq:normalizedMap i q=∞ ∨ normalizedMap i q=(0:ℂ) ∨
      normalizedMap i q=(1:ℂ) ∨ normalizedMap i q=(branchParameter i:ℂ)) :
    ∃(e:OpenPartialHomeomorph (CharacterBase i) ℂ)
      (b:OpenPartialHomeomorph (OnePoint ℂ) ℂ),
      q∈e.source ∧ normalizedMap i q∈b.source ∧ e q=0 ∧ b (normalizedMap i q)=0 ∧
      (∀x∈e.source,normalizedMap i x∈b.source ∧ b (normalizedMap i x)=(e x)^2) ∧
      (∀x∈e.source,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e x) ∧
      (∀z∈e.target,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm z) ∧
      (∀x∈b.source,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω b x) ∧
      (∀z∈b.target,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω b.symm z) := by
  have hbranch:toMaximal i q∈CharacterBranchValues i:=
    (actual_branch_values i (toMaximal i q)).mpr hq
  obtain ⟨p,rfl⟩:=toCharacter_surjective i q
  have hcard:Nat.card {y:CharacterBase i // toMaximal i y=
      PELOriginalMaximalQuotient318.projection p}=1:=hbranch
  have hp:p∈nontrivialStabilizerLocus:=by
    by_contra hp
    have hh:=regular_fiber_card i p hp
    omega
  obtain ⟨j,hj⟩:=(original_locus_union p).mp hp
  have hv:InertiaLabels318.fiveLabels j i≠0:=by
    intro he
    have hh:=branch_fiber_card i j p hj
    rw [if_pos he] at hh
    omega
  obtain ⟨τ,rfl⟩:=PELUnlevelledComplexBase318.projection_surjective p
  obtain ⟨U,e,b₀,hU,hpU,hes,hb,hzero,hmodel,hehol⟩:=
    PELOriginalCharacterLocalSquare318.visible_local_square i j τ hj hv
  let b:OpenPartialHomeomorph (OnePoint ℂ) ℂ:=
    (coordinate i).symm.toOpenPartialHomeomorph.trans b₀
  have he:OriginalChart i e:=⟨U,hU,hes,hehol⟩
  have hqe:toCharacter i (PELUnlevelledComplexBase318.projection τ)∈e.source:=by
    rw [hes]
    exact ⟨_,hpU,rfl⟩
  have hcoord (x:CharacterBase i) : (coordinate i).symm (normalizedMap i x)=toMaximal i x:=
    (coordinate i).symm_apply_apply _
  have hnew:∀x∈e.source,normalizedMap i x∈b.source ∧ b (normalizedMap i x)=(e x)^2:=by
    intro x hx
    constructor
    · refine ⟨mem_univ _,?_⟩
      change (coordinate i).symm (normalizedMap i x)∈b₀.source
      rw [hcoord]
      exact (hmodel x hx).1
    · change b₀ ((coordinate i).symm (normalizedMap i x))=(e x)^2
      rw [hcoord]
      exact (hmodel x hx).2
  have hbhol:∀x∈b.source,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω b x:=by
    intro x hx
    exact (PELOriginalMaximalCharts318.original_chart_holomorphic b₀ hb
      ((coordinate i).symm x) hx.2).comp x ((coordinate_biholomorphic i).2 x)
  refine ⟨e,b,hqe,(hnew _ hqe).1,hzero,?_,hnew,?_,?_,hbhol,?_⟩
  · rw [(hnew _ hqe).2,hzero,zero_pow (by decide : 2≠0)]
  · exact fun x hx=>PELOriginalCharacterCharts318.original_chart_holomorphic i e he x hx
  · exact fun z hz=>PELOriginalCharacterCharts318.original_inverse_holomorphic i e he z hz
  · intro z hz
    have hh:=ComplexCurvePartialInverse318.inverse_at b (b.symm z) (b.map_target hz)
      (hbhol _ (b.map_target hz))
    simpa only [b.right_inv hz] using hh
end PELOriginalNormalizedBranchSquare318
