module
public import PELOriginalRegularLegendreHomeomorph318
public section
noncomputable section
namespace PELOriginalRegularCoordinateHolomorphy318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalRegularCoverPatches318
open PELOriginalGluedLegendreMap318 PELOriginalNormalizedDoubleCover318
open ComplexSphereCharts318
variable (i : Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

@[expose] def baseCoordinate (x : CharacterBase i) : ℂ := affine (normalizedMap i x)
lemma base_patch (k : Index) (z : patchDomain i k.1) :
    baseCoordinate i (patch i k z)=z.val := by
  rw [baseCoordinate,patch_projection,affine_coe]
lemma base_holomorphic (x : CharacterBase i) (hx : x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (baseCoordinate i) x := by
  obtain ⟨z,hz,_,_,_⟩:=hx
  have ha : normalizedMap i x∈affine.source := by rw [hz];exact affine_mem z
  have hc:=contMDiffAt_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas (show affine∈atlas ℂ (OnePoint ℂ) from ⟨false,rfl⟩)) ha
  exact hc.comp x (PELOriginalNormalizedDoubleCover318.holomorphic i x)

/-- On an actual open sheet the original glued coordinates are functions
of the genuine holomorphic normalized base coordinate. This upgrades
sheet formulas to holomorphy in the UNCHANGED source manifold atlas. -/
lemma coordinates_on_patch (k : Index) (x : CharacterBase i) (hx : x∈range (patch i k)) :
    coordinates i x=(baseCoordinate i x,value i k (baseCoordinate i x)) := by
  obtain ⟨z,rfl⟩:=hx
  rw [coordinates_patch,base_patch]

theorem coordinates_holomorphic (x : CharacterBase i) (hx : x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q=>(coordinates i q).1) x ∧
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun q=>(coordinates i q).2) x := by
  obtain ⟨k,z,hz⟩:=patches_cover i x hx
  have hb:=base_holomorphic i x hx
  have hxrange : x∈range (patch i k) := ⟨z,hz⟩
  have hn := (patch_open i k).isOpen_range.mem_nhds hxrange
  have hbase : baseCoordinate i x=z.val := by rw [←hz,base_patch]
  have hv : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (value i k) (baseCoordinate i x) := by
    rw [hbase]
    exact contMDiffAt_iff_contDiffAt.mpr ((value_analytic i k z.val z.property).contDiffAt)
  constructor
  · apply hb.congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    exact congrArg Prod.fst (coordinates_on_patch i k q hq)
  · apply (hv.comp x hb).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    exact congrArg Prod.snd (coordinates_on_patch i k q hq)
end PELOriginalRegularCoordinateHolomorphy318
