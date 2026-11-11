module
public import PELOriginalCharacterLocalSquare318
public section
noncomputable section
namespace PELOriginalCharacterOmittedSquare318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopology318
open PELOriginalBranchLabels318 PELCoarseInertiaCoordinate318
open OpenQuotientSameFibers318 OpenSquaredChart318
open QuaternionicJointPeriodTopology318 PELInertiaSquaredCoordinate318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1600000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- At an omitted label, local full orbits and local character-kernel
orbits are the SAME actual equivalence relation. -/
lemma omitted_local_fibers (i : Fin 4) (j : Fin 5) (p : UnlevelledBase)
    (hp : p ∈ fixedLocus j) (homit : InertiaLabels318.fiveLabels j i = 0) :
    ∃ V : Set UnlevelledBase, V ∈ 𝓝 p ∧
      ∀ x ∈ V, ∀ y ∈ V,
        toCharacter i x = toCharacter i y ↔
          PELOriginalMaximalQuotient318.projection x =
            PELOriginalMaximalQuotient318.projection y := by
  obtain ⟨V,hV,hrel⟩ := PELMaximalLocalOrbit318.local_orbit_relation j p hp
  refine ⟨V,hV,?_⟩
  intro x hx y hy
  constructor
  · exact fun he => congrArg (toMaximal i) he
  · intro he
    rcases (hrel x hx y hy).mp he with hxy | hxy
    · exact congrArg (toCharacter i) hxy
    · apply (toCharacter_eq_iff i x y).mpr
      refine ⟨⟨Multiplicative.ofAdd (InertiaLabels318.fiveLabels j),?_⟩,hxy.symm⟩
      change Multiplicative.ofAdd (InertiaLabels318.fiveLabels j i) = 1
      rw [homit]
      rfl

/-- A genuine chart of the SAME character quotient at omitted inertia.
The original curve-to-character map is locally z² here. In contrast, at
visible inertia that map was locally z, and character-to-maximal was z². -/
theorem omitted_chart (i : Fin 4) (j : Fin 5) (τ : HalfPlane)
    (hp : PELUnlevelledComplexBase318.projection τ ∈ fixedLocus j)
    (homit : InertiaLabels318.fiveLabels j i = 0) :
    ∃ (U : Set UnlevelledBase) (e : OpenPartialHomeomorph (CharacterBase i) ℂ),
      IsOpen U ∧ PELUnlevelledComplexBase318.projection τ ∈ U ∧
      e.source = toCharacter i '' U ∧
      (∀ x ∈ U,e (toCharacter i x) = squaredCoordinate τ x) ∧
      ∀ x ∈ U, ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
        (fun y => e (toCharacter i y)) x := by
  obtain ⟨V,hV,hrel⟩ := omitted_local_fibers i j _ hp homit
  obtain ⟨W,hW,hpW,hWsub,hWfib⟩ :=
    PELMaximalSquaredLocalFibers318.original_squared_quotient_fibers j τ hp
  let U := interior V ∩ W
  have hU : IsOpen U := isOpen_interior.inter hW
  have hpU : PELUnlevelledComplexBase318.projection τ ∈ U :=
    ⟨mem_interior_iff_mem_nhds.mpr hV,hpW⟩
  have hsub : U ⊆ (inertiaChart τ).source := fun _ hx => hWsub hx.2
  have hfib : ∀ x ∈ U, ∀ y ∈ U,
      toCharacter i x = toCharacter i y ↔ squaredCoordinate τ x = squaredCoordinate τ y := by
    intro x hx y hy
    exact (hrel x (interior_subset hx.1) y (interior_subset hy.1)).trans
      (hWfib x hx.2 y hy.2)
  let q := imageMap (toCharacter i) U
  let f := imageMap (squaredCoordinate τ) U
  have hq : IsOpenQuotientMap q := imageMap_openQuotient _ U
    (toCharacter_continuous i).continuousOn
    ((toCharacter_open i).comp hU.isOpenMap_subtype_val)
  have hf : IsOpenQuotientMap f := square_image_quotient (inertiaChart τ) U hU hsub
  have hr : ∀ x y : U,q x = q y ↔ f x = f y := by
    intro x y
    constructor
    · intro he
      exact Subtype.ext ((hfib x x.property y y.property).mp (congrArg Subtype.val he))
    · intro he
      exact Subtype.ext ((hfib x x.property y y.property).mpr (congrArg Subtype.val he))
  let H := homeomorph q f hq.isQuotientMap hf.isQuotientMap hr
  have hQ := toCharacter_open i U hU
  have hF := square_image_open (inertiaChart τ) U hU hsub
  let hne : Nonempty (toCharacter i '' U) :=
    ⟨⟨toCharacter i (PELUnlevelledComplexBase318.projection τ),⟨_,hpU,rfl⟩⟩⟩
  let e := OpenImageHomeomorphChart318.extend _ _ hQ hF hne H
  have hval : ∀ x ∈ U,e (toCharacter i x) = squaredCoordinate τ x := by
    intro x hx
    have hH := homeomorph_value q f hq.isQuotientMap hf.isQuotientMap hr (⟨x,hx⟩ : U)
    have he := OpenImageHomeomorphChart318.extend_value _ _ hQ hF hne H
      (⟨toCharacter i x,⟨x,hx,rfl⟩⟩ : toCharacter i '' U)
    exact he.trans (congrArg Subtype.val hH)
  refine ⟨U,e,hU,hpU,OpenImageHomeomorphChart318.extend_source _ _ hQ hF hne H,hval,?_⟩
  intro x hx
  have hh := (chart_holomorphic τ x (hsub hx)).pow 2
  apply hh.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hval y hy
end PELOriginalCharacterOmittedSquare318
