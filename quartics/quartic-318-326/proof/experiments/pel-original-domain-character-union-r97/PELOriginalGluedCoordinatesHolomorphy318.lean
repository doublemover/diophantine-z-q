module
public import PELOriginalRegularLegendreHomeomorph318
public section
noncomputable section
namespace PELOriginalGluedCoordinatesHolomorphy318
open Set Filter
open scoped Topology OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalRegularCoverPatches318 PELOriginalGluedLegendreMap318
open ComplexSphereCharts318
local instance (i:Fin 4) : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance (i:Fin 4) : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- The actual affine normalized coordinate is holomorphic at every
original regular point, in the unchanged original source atlas. -/
lemma base_coordinate_holomorphic (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun p=>affine (normalizedMap i p)) x := by
  rcases hx with ⟨z,hz,_,_,_⟩
  have hm:affine∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=
    IsManifold.subset_maximalAtlas (show affine∈atlas ℂ (OnePoint ℂ) from ⟨false,rfl⟩)
  have hp:normalizedMap i x∈affine.source:=by rw [hz];exact affine_mem z
  exact (contMDiffAt_of_mem_maximalAtlas hm hp).comp x (PELOriginalNormalizedDoubleCover318.holomorphic i x)

/-- Locality upgrades the actual patch formulas to holomorphy on the
original atlas. The open source image is a genuine neighborhood, and
its inverse coordinate is the original normalized projection. -/
theorem y_holomorphic (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun p=>(coordinates i p).2) x := by
  obtain ⟨k,z,rfl⟩:=patches_cover i x hx
  have ht:affine (normalizedMap i (patch i k z))=z.val:=by rw [patch_projection,affine_coe]
  have hv:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (value i k)
      (affine (normalizedMap i (patch i k z))):=by
    rw [ht]
    exact contMDiffAt_iff_contDiffAt.mpr (value_analytic i k z.val z.property).contDiffAt
  have hh:=hv.comp (patch i k z) (base_coordinate_holomorphic i _ (patch_regular i k z))
  apply hh.congr_of_eventuallyEq
  filter_upwards [(patch_open i k).isOpen_range.mem_nhds (mem_range_self z)] with p hp
  obtain ⟨w,rfl⟩:=hp
  rw [coordinates_patch,patch_projection,affine_coe]

lemma t_holomorphic (i:Fin 4) (x:CharacterBase i) (hx:x∈Regular i) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun p=>(coordinates i p).1) x := by
  apply (base_coordinate_holomorphic i x hx).congr_of_eventuallyEq
  filter_upwards [(regular_open i).mem_nhds hx] with p hp
  rw [←coordinates_projection i p hp,affine_coe]

/-- Every holomorphic curve in the ORIGINAL source sees actual analytic
Legendre coordinates at each regular image point. This is the interface
for the original literal branch parametrizations, not a transported atlas. -/
theorem along_holomorphic_curve (i:Fin 4) (g:ℂ→CharacterBase i) (z:ℂ)
    (hg:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g z) (hz:g z∈Regular i) :
    AnalyticAt ℂ (fun w=>(coordinates i (g w)).1) z ∧
      AnalyticAt ℂ (fun w=>(coordinates i (g w)).2) z := by
  constructor
  · exact (contMDiffAt_iff_contDiffAt.mp ((t_holomorphic i (g z) hz).comp z hg)).analyticAt
  · exact (contMDiffAt_iff_contDiffAt.mp ((y_holomorphic i (g z) hz).comp z hg)).analyticAt
end PELOriginalGluedCoordinatesHolomorphy318
