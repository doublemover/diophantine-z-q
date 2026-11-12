module
public import PELOriginalInvolutionLocalCover318
public section
noncomputable section
namespace PELOriginalInvolutionComplexAtlas318
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318
open PELOriginalCharacterTopologicalAtlas318 PELOriginalCharacterComplexAtlas318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1800000
variable (i : Fin 4)
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
local instance : ChartedSpace ℂ (CharacterBase i) := characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) := character_manifold i

@[expose] def localSheet (p : InvolutionBase i) :
    OpenPartialHomeomorph (InvolutionBase i) (CharacterBase i) :=
  Classical.choose (local_cover i p)
lemma localSheet_center (p : InvolutionBase i) : p ∈ (localSheet i p).source :=
  (Classical.choose_spec (local_cover i p)).1
lemma localSheet_value (p x : InvolutionBase i) (hx : x ∈ (localSheet i p).source) :
    localSheet i p x = toCharacterBase i x :=
  (Classical.choose_spec (local_cover i p)).2 x hx

/-- Pull the EXISTING character complex chart back along the constructed
local sheet of the actual four-map. No genus-one uniformization is assumed. -/
@[expose] def sheetChart (p : InvolutionBase i) :
    OpenPartialHomeomorph (InvolutionBase i) ℂ :=
  (localSheet i p).trans (chartAt ℂ (toCharacterBase i p))
lemma sheetChart_center (p : InvolutionBase i) : p ∈ (sheetChart i p).source := by
  refine ⟨localSheet_center i p,?_⟩
  rw [localSheet_value i p p (localSheet_center i p)]
  exact mem_chart_source ℂ _
lemma sheetChart_value (p x : InvolutionBase i) (hx : x ∈ (sheetChart i p).source) :
    sheetChart i p x = chartAt ℂ (toCharacterBase i p) (toCharacterBase i x) := by
  change chartAt ℂ (toCharacterBase i p) (localSheet i p x) = _
  rw [localSheet_value i p x hx.1]
lemma sheetChart_over (p : InvolutionBase i) (z : ℂ)
    (hz : z ∈ (sheetChart i p).target) :
    toCharacterBase i ((sheetChart i p).symm z) =
      (chartAt ℂ (toCharacterBase i p)).symm z := by
  have hsrc := (localSheet i p).map_target hz.2
  have hv := localSheet_value i p
    ((localSheet i p).symm ((chartAt ℂ (toCharacterBase i p)).symm z)) hsrc
  exact hv.symm.trans ((localSheet i p).right_inv hz.2)

/-- Original sheet transitions reduce locally to the EXISTING character
surface transitions. All local sheet identities hold on their whole domains. -/
theorem transition_contDiffAt (p q : InvolutionBase i) (z : ℂ)
    (hz : z ∈ ((sheetChart i p).symm.trans (sheetChart i q)).source) :
    ContDiffAt ℂ ω ((sheetChart i p).symm.trans (sheetChart i q)) z := by
  let A := chartAt ℂ (toCharacterBase i p)
  let B := chartAt ℂ (toCharacterBase i q)
  have hzA : z ∈ A.target := hz.1.1
  have hmap := sheetChart_over i p z hz.1
  have hBsrc : A.symm z ∈ B.source := by
    have hh := hz.2.2
    rw [localSheet_value i q _ hz.2.1,hmap] at hh
    exact hh
  have hA := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (toCharacterBase i p)) hzA
  have hB := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (toCharacterBase i q)) hBsrc
  have hc : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w => B (A.symm w)) z := hB.comp z hA
  apply (contMDiffAt_iff_contDiffAt.mp hc).congr_of_eventuallyEq
  filter_upwards [((sheetChart i p).symm.trans (sheetChart i q)).open_source.mem_nhds hz] with w hw
  change sheetChart i q ((sheetChart i p).symm w) = B (A.symm w)
  rw [sheetChart_value i q _ hw.2,sheetChart_over i p w hw.1]

@[expose,instance_reducible] def involutionCharts : ChartedSpace ℂ (InvolutionBase i) where
  atlas := Set.range (sheetChart i)
  chartAt := sheetChart i
  mem_chart_source := sheetChart_center i
  chart_mem_atlas p := ⟨p,rfl⟩

/-- A complex atlas on the ACTUAL original involution quotient topology,
not an abstract genus-one curve or a chosen published model. -/
theorem involution_manifold :
    letI := involutionCharts i
    IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i) := by
  letI := involutionCharts i
  apply isManifold_of_contDiffOn
  rintro e f ⟨p,rfl⟩ ⟨q,rfl⟩
  have hh : ContDiffOn ℂ ω ((sheetChart i p).symm.trans (sheetChart i q))
      ((sheetChart i p).symm.trans (sheetChart i q)).source :=
    fun z hz => (transition_contDiffAt i p q z hz).contDiffWithinAt
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using hh

local instance : ChartedSpace ℂ (InvolutionBase i) := involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i) := involution_manifold i

lemma sheetChart_maximal (p : InvolutionBase i) :
    sheetChart i p ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (InvolutionBase i) :=
  IsManifold.subset_maximalAtlas ⟨p,rfl⟩

/-- The original everywhere-four-map is holomorphic for the compatible
actual atlases, rather than only being a topological finite cover. -/
theorem toCharacterBase_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toCharacterBase i) := by
  intro p
  let A := chartAt ℂ (toCharacterBase i p)
  let e := sheetChart i p
  have hp := sheetChart_center i p
  have hzA : e p ∈ A.target := by
    rw [sheetChart_value i p p hp]
    exact A.map_source (mem_chart_source ℂ _)
  have hE := contMDiffAt_of_mem_maximalAtlas (sheetChart_maximal i p) hp
  have hA := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (toCharacterBase i p)) hzA
  apply (hA.comp p hE).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with x hx
  have hxA : toCharacterBase i x ∈ A.source := by
    have hh := hx.2
    rw [localSheet_value i p x hx.1] at hh
    exact hh
  rw [sheetChart_value i p x hx]
  exact (A.left_inv hxA).symm

/-- The ORIGINAL curve-to-involution quotient is holomorphic, including
its old ramification centers. This verifies compatibility with the original
complex curve, not only with the character target used to build the atlas. -/
theorem toInvolution_holomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (toInvolution i) := by
  intro x
  let p := toInvolution i x
  let e := sheetChart i p
  let A := chartAt ℂ (toCharacterBase i p)
  have hp := sheetChart_center i p
  have hA := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (toCharacterBase i p)) (mem_chart_source ℂ _)
  have hC := character_projection_holomorphic i x
  have hAC : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
      (fun y => A (toCharacter i y)) x := hA.comp x hC
  have hI := contMDiffAt_symm_of_mem_maximalAtlas (sheetChart_maximal i p) (e.map_source hp)
  have hI' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm (A (toCharacter i x)) := by
    simpa only [sheetChart_value i p p hp] using hI
  apply (hI'.comp x hAC).congr_of_eventuallyEq
  filter_upwards [(toInvolution_continuous i).continuousAt.tendsto.eventually
    (e.open_source.mem_nhds hp)] with y hy
  have hv := sheetChart_value i p (toInvolution i y) hy
  exact (e.left_inv hy).symm.trans (congrArg e.symm hv)
end PELOriginalInvolutionComplexAtlas318
