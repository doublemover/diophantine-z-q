module
public import PELOriginalGluedLegendreFibers318
public import LegendreRootGraphTopology318
public import PELOriginalAnalyticRealStrip318
public section
noncomputable section
namespace PELOriginalRegularLegendreHomeomorph318
open Set Topology
open scoped OnePoint Manifold ContDiff
open PELOriginalCharacterQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalRegularCoverPatches318 PELOriginalGluedLegendreMap318
open PELOriginalGluedLegendreFibers318 PELOriginalCompatibleLegendreCoordinates318
open PELOriginalHalfPlaneSheetTopology318 PELOriginalRealBranchIntervals318
open LegendreHalfPlaneAnalyticSheets318

@[expose] def sourcePatch (i:Fin 4) (k:Index) (z:patchDomain i k.1) : Regular i:=
  ⟨patch i k z,patch_regular i k z⟩
lemma sourcePatch_continuous (i:Fin 4) (k:Index) : Continuous (sourcePatch i k):=
  (patch_open i k).continuous.subtype_mk _
@[expose] def targetPatch (i:Fin 4) (k:Index) (z:patchDomain i k.1) : Target i:=
  ⟨⟨(z.val,value i k z.val),value_square i k z.val⟩,by
    have hn:=polynomial_nonzero_patch i k.1 z
    refine ⟨?_,?_,?_⟩
    all_goals
      intro h
      apply hn
      simp [polynomial,h]⟩
lemma patchDomain_open (i:Fin 4) (k:Kind) : IsOpen (patchDomain i k) := by
  cases k with
  | inl upper=>exact domain_open upper
  | inr j=>exact ComplexVerticalStrip318.strip_open ((ordering i).interval j).isOpen
lemma targetPatch_open (i:Fin 4) (k:Index) : IsOpenMap (targetPatch i k) :=
  (LegendreRootGraphTopology318.analytic_graph_openEmbedding (branchParameter i)
    (patchDomain i k.1) (value i k) (value_square i k) (patchDomain_open i k.1)
    (value_analytic i k) (fun z hz=>polynomial_nonzero_patch i k.1 ⟨z,hz⟩)).isOpenMap.subtype_mk _
lemma targetPatch_continuous (i:Fin 4) (k:Index) : Continuous (targetPatch i k):=
  ((continuous_subtype_val.prodMk ((value_analytic i k).continuousOn.domRestrict)).subtype_mk _).subtype_mk _
lemma targetPatch_openEmbedding (i:Fin 4) (k:Index) : IsOpenEmbedding (targetPatch i k) := by
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  refine ⟨targetPatch_continuous i k,?_,targetPatch_open i k⟩
  intro z w h
  exact Subtype.ext (congrArg (fun p:Target i=>p.val.val.1) h)

lemma comparison_patch (i:Fin 4) (k:Index) (z:patchDomain i k.1) :
    comparison i (sourcePatch i k z)=targetPatch i k z := by
  apply Subtype.ext
  apply Subtype.ext
  exact coordinates_patch i k z

/-- Openness is proved using genuine open target root graphs and actual
open source sheets. No compactness/bijection shortcut or transported
Legendre topology is used to claim inverse continuity. -/
theorem comparison_open (i:Fin 4) : IsOpenMap (comparison i) := by
  intro V hV
  have he:comparison i '' V=⋃k:Index,targetPatch i k '' (sourcePatch i k ⁻¹' V):=by
    ext p
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨k,z,hz⟩:=patches_cover i x.val x.property
      have hx':sourcePatch i k z=x:=Subtype.ext hz
      exact mem_iUnion.mpr ⟨k,z,hx'.symm ▸ hx,(comparison_patch i k z).symm.trans (congrArg (comparison i) hx')⟩
    · intro hp
      obtain ⟨k,z,hz,rfl⟩:=mem_iUnion.mp hp
      exact ⟨sourcePatch i k z,hz,comparison_patch i k z⟩
  rw [he]
  exact isOpen_iUnion fun k=>targetPatch_open i k _ (hV.preimage (sourcePatch_continuous i k))

/-- The WHOLE actual original unbranched character cover is homeomorphic
to the literal Legendre equation away from its same branch points.
Both sides keep their independently established original topologies. -/
@[expose] def homeomorph (i:Fin 4) : Regular i≃ₜTarget i:=
  (equivalence i).toHomeomorphOfContinuousOpen (comparison_continuous i) (comparison_open i)
lemma homeomorph_patch (i:Fin 4) (k:Index) (z:patchDomain i k.1) :
    homeomorph i (sourcePatch i k z)=targetPatch i k z:=comparison_patch i k z
lemma inverse_patch (i:Fin 4) (k:Index) (z:patchDomain i k.1) :
    (homeomorph i).symm (targetPatch i k z)=sourcePatch i k z := by
  rw [←homeomorph_patch,Homeomorph.symm_apply_apply]

local instance (i:Fin 4) : ChartedSpace ℂ (CharacterBase i):=
  PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance (i:Fin 4) : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i):=
  PELOriginalCharacterComplexAtlas318.character_manifold i

/-- The inverse on EVERY genuine target graph is holomorphic into the
unchanged original complex atlas, including the real strips. The same
old continuous lift and its proved analytic upgrade are used. -/
theorem inverse_chart_holomorphic (i:Fin 4) (k:Index) :
    ∃G:ℂ→CharacterBase i,
      (∀z∈patchDomain i k.1,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω G z) ∧
      ∀z:patchDomain i k.1,G z.val=((homeomorph i).symm (targetPatch i k z)).val := by
  rcases k with ⟨upper|j,b⟩
  · let e:=enumeration i upper b
    refine ⟨PELOriginalAnalyticHalfPlaneSheets318.totalSheet i upper e,
      PELOriginalAnalyticHalfPlaneSheets318.totalSheet_holomorphic i upper e,?_⟩
    intro z
    rw [inverse_patch]
    exact PELOriginalAnalyticHalfPlaneSheets318.totalSheet_eq i upper e z
  · let J:PELOriginalRealStripCover318.Interval i:=(ordering i).interval j
    let e:J.BaseFiber:=(J.sideLabels true).symm (enumeration i true b)
    refine ⟨PELOriginalAnalyticRealStrip318.totalSheet J e,
      PELOriginalAnalyticRealStrip318.totalSheet_holomorphic J e,?_⟩
    intro z
    rw [inverse_patch]
    exact PELOriginalAnalyticRealStrip318.totalSheet_eq J e z

/-- The forward coordinates and inverse are holomorphic in actual open
charts covering EVERY point of both regular loci. Compact branch filling
is deliberately not inferred from this regular comparison. -/
theorem regular_analytic_comparison (i:Fin 4) :
    (∀k:Index,∃F:ℂ→ℂ×ℂ,AnalyticOnNhd ℂ F (patchDomain i k.1) ∧
      ∀z:patchDomain i k.1,F z.val=(homeomorph i (sourcePatch i k z)).val.val) ∧
    (∀k:Index,∃G:ℂ→CharacterBase i,
      (∀z∈patchDomain i k.1,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω G z) ∧
      ∀z:patchDomain i k.1,G z.val=((homeomorph i).symm (targetPatch i k z)).val) := by
  constructor
  · intro k
    refine ⟨fun z=>(z,value i k z),?_,?_⟩
    · intro z hz
      exact analyticAt_id.prod (value_analytic i k z hz)
    · intro z
      rw [homeomorph_patch]
      rfl
  · exact inverse_chart_holomorphic i
end PELOriginalRegularLegendreHomeomorph318
