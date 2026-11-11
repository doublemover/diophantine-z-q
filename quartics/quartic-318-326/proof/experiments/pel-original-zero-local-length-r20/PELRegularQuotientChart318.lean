module
public import OpenImageHomeomorphChart318
public section
noncomputable section
namespace PELRegularQuotientChart318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318 PELOriginalBranchLabels318
open OpenQuotientSameFibers318 OpenSquaredChart318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1800000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- Around every regular original point, the FULL quotient projection is
injective on a constructed open neighborhood inside its original chart. -/
theorem regular_domain (p : UnlevelledBase) (hp : p∉nontrivialStabilizerLocus) :
    ∃ U : Set UnlevelledBase,IsOpen U ∧ p∈U ∧ U⊆(chartAt ℂ p).source ∧
      Set.InjOn PELOriginalMaximalQuotient318.projection U := by
  obtain ⟨V,hV,hstab⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self Labels p
  let U := interior V∩(chartAt ℂ p).source
  refine ⟨U,isOpen_interior.inter (chartAt ℂ p).open_source,
    ⟨mem_interior_iff_mem_nhds.mpr hV,mem_chart_source ℂ p⟩,Set.inter_subset_right,?_⟩
  intro x hx y hy hq
  obtain ⟨g,hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff x y).mp hq
  have hfix := hstab g ⟨x,⟨⟨y,interior_subset hy.1,hg⟩,interior_subset hx.1⟩⟩
  have hg1 : g=1 := by
    by_contra hne
    apply hp
    refine ⟨Multiplicative.toAdd g,?_,hfix⟩
    intro hz
    exact hne (congrArg Multiplicative.ofAdd hz)
  simpa only [hg1,one_smul] using hg.symm

/-- Genuine regular quotient chart, using the unchanged original source
chart and actual open quotient map. -/
theorem exists_regular_chart (p : UnlevelledBase) (hp : p∉nontrivialStabilizerLocus) :
    ∃ (U : Set UnlevelledBase) (e : OpenPartialHomeomorph MaximalBase ℂ),
      IsOpen U ∧ p∈U ∧ e.source=PELOriginalMaximalQuotient318.projection '' U ∧
      (∀ x∈U,e (PELOriginalMaximalQuotient318.projection x)=chartAt ℂ p x) ∧
      ∀ x∈U,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
        (fun y => e (PELOriginalMaximalQuotient318.projection y)) x := by
  obtain ⟨U,hU,hpU,hsub,hinj⟩ := regular_domain p hp
  let A := chartAt ℂ p
  let q := imageMap PELOriginalMaximalQuotient318.projection U
  let f := imageMap A U
  have hq : IsOpenQuotientMap q := PELDescendedInertiaChart318.projection_image_quotient U hU
  have hf : IsOpenQuotientMap f := imageMap_openQuotient A U
    (A.continuousOn.mono hsub) (restricted_chart_open A U hU hsub)
  have hrel : ∀ x y : U,q x=q y ↔ f x=f y := by
    intro x y
    constructor
    · intro he
      have hxy := hinj x.property y.property (congrArg Subtype.val he)
      exact Subtype.ext (congrArg A hxy)
    · intro he
      have hxy := A.injOn (hsub x.property) (hsub y.property) (congrArg Subtype.val he)
      exact Subtype.ext (congrArg PELOriginalMaximalQuotient318.projection hxy)
  let E := homeomorph q f hq.isQuotientMap hf.isQuotientMap hrel
  have hQ := PELOriginalMaximalQuotient318.projection_open U hU
  have hF := A.isOpen_image_of_subset_source hU hsub
  let he : Nonempty (PELOriginalMaximalQuotient318.projection '' U) :=
    ⟨⟨PELOriginalMaximalQuotient318.projection p,⟨p,hpU,rfl⟩⟩⟩
  let e := OpenImageHomeomorphChart318.extend _ _ hQ hF he E
  have hval : ∀ x∈U,e (PELOriginalMaximalQuotient318.projection x)=A x := by
    intro x hx
    have hE := homeomorph_value q f hq.isQuotientMap hf.isQuotientMap hrel (⟨x,hx⟩:U)
    have hv := OpenImageHomeomorphChart318.extend_value _ _ hQ hF he E
      (⟨PELOriginalMaximalQuotient318.projection x,⟨x,hx,rfl⟩⟩:
        PELOriginalMaximalQuotient318.projection '' U)
    exact hv.trans (congrArg Subtype.val hE)
  refine ⟨U,e,hU,hpU,OpenImageHomeomorphChart318.extend_source _ _ hQ hF he E,hval,?_⟩
  intro x hx
  have hA := contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) (hsub hx)
  apply hA.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hval y hy
end PELRegularQuotientChart318
