module
public import PELOriginalCompletedLegendreBijection318
public import PELOriginalLiteralBranchParameters318
public section
noncomputable section
namespace PELOriginalInfinityBranchSource318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRegularCoverPatches318
open SphereInversion318
variable (i:Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i

@[expose] def parameter (p:CharacterBase i) (hp:normalizedMap i p=∞):=
  PELOriginalLiteralBranchParameters318.infinity i p hp
@[expose] def source (p:CharacterBase i) (hp:normalizedMap i p=∞) : ℂ→CharacterBase i:=
  fun w=>(parameter i p hp).chart.symm ((parameter i p hp).inverseChange w)
lemma source_zero (p:CharacterBase i) (hp:normalizedMap i p=∞) : source i p hp 0=p := by
  let P:=parameter i p hp
  change P.chart.symm (P.inverseChange 0)=p
  rw [P.inverse_zero,←P.center_zero]
  exact P.chart.left_inv P.center_mem
lemma source_holomorphic (p:CharacterBase i) (hp:normalizedMap i p=∞) :
    ∀ᶠ w in 𝓝 (0:ℂ),ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (source i p hp) w := by
  let P:=parameter i p hp
  filter_upwards [P.projection,P.inverse_analytic.eventually_analyticAt] with w hw ha
  exact (P.chart_inverse_holomorphic _ hw.1).comp w
    (contMDiffAt_iff_contDiffAt.mpr ha.contDiffAt)
lemma source_projection (p:CharacterBase i) (hp:normalizedMap i p=∞) :
    ∀ᶠ w in 𝓝 (0:ℂ),normalizedMap i (source i p hp w)=inversion (w^2:ℂ) :=
  (parameter i p hp).projection.mono fun _ hw=>hw.2
lemma source_punctured_projection (p:CharacterBase i) (hp:normalizedMap i p=∞) :
    ∀ᶠ w in 𝓝[≠] (0:ℂ),normalizedMap i (source i p hp w)=((w^2)⁻¹:ℂ) := by
  filter_upwards [(source_projection i p hp).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with w hw hn
  rw [hw,inversion_coe (pow_ne_zero 2 hn)]

/-- Every sufficiently small nonzero ORIGINAL infinity parameter is in
the SAME actual finite regular locus. Excluding other branches is proved
by their nonzero reciprocal coordinates, not presumed from a picture. -/
lemma source_regular (p:CharacterBase i) (hp:normalizedMap i p=∞) :
    ∀ᶠ w in 𝓝[≠] (0:ℂ),source i p hp w∈Regular i := by
  have hs:ContinuousAt (fun w:ℂ=>w^2) 0:=by fun_prop
  have h1:∀ᶠ w in 𝓝 (0:ℂ),w^2≠1:=hs.eventually_ne (by norm_num)
  have hl:∀ᶠ w in 𝓝 (0:ℂ),w^2≠(branchParameter i)⁻¹:=
    hs.eventually_ne (by simpa only [zero_pow (by decide:2≠0)] using
      (inv_ne_zero (branchParameter_nonexceptional i).1).symm)
  filter_upwards [source_punctured_projection i p hp,h1.filter_mono nhdsWithin_le_nhds,
    hl.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with w hw h1w hlw hn
  refine ⟨(w^2)⁻¹,hw,inv_ne_zero (pow_ne_zero 2 hn),?_,?_⟩
  · intro h
    apply h1w
    simpa only [inv_inv,inv_one] using congrArg (fun z:ℂ=>z⁻¹) h
  · intro h
    apply hlw
    simpa only [inv_inv] using congrArg (fun z:ℂ=>z⁻¹) h
end PELOriginalInfinityBranchSource318
