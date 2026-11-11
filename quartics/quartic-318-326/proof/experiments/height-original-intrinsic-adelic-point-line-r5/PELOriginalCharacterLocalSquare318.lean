module
public import PELOriginalCharacterTopology318
public section
noncomputable section
namespace PELOriginalCharacterLocalSquare318
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

/-- At a visible inertia point the ENTIRE original character kernel acts freely. -/
lemma visible_kernel_free (i : Fin 4) (j : Fin 5) (p : UnlevelledBase)
    (hp : p ∈ fixedLocus j) (hvisible : InertiaLabels318.fiveLabels j i ≠ 0)
    (k : (character i).ker) (hk : k • p = p) : k = 1 := by
  apply Subtype.ext
  rcases (locus_stabilizer_iff j p hp (Multiplicative.toAdd (k : Labels))).mp hk with h0 | hj
  · exact congrArg Multiplicative.ofAdd h0
  · have hlabel : (k : Labels) = Multiplicative.ofAdd (InertiaLabels318.fiveLabels j) :=
      congrArg Multiplicative.ofAdd hj
    have hχ : character i (k : Labels) = 1 := k.property
    rw [hlabel] at hχ
    exact False.elim (hvisible (congrArg Multiplicative.toAdd hχ))

/-- Descend ANY original chart at a kernel-free point, inside a specified
original open neighborhood. The quotient source is not replaced. -/
theorem free_chart (i : Fin 4) (p : UnlevelledBase)
    (E : OpenPartialHomeomorph UnlevelledBase ℂ) (hpE : p ∈ E.source)
    (W : Set UnlevelledBase) (hW : IsOpen W) (hpW : p ∈ W)
    (hfree : ∀ k : (character i).ker, k • p = p → k = 1) :
    ∃ (U : Set UnlevelledBase) (e : OpenPartialHomeomorph (CharacterBase i) ℂ),
      IsOpen U ∧ p ∈ U ∧ U ⊆ W ∧ U ⊆ E.source ∧
      e.source = toCharacter i '' U ∧
      ∀ x ∈ U, e (toCharacter i x) = E x := by
  obtain ⟨V,hV,hstab⟩ :=
    ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self (character i).ker p
  let U := (interior V ∩ E.source) ∩ W
  have hU : IsOpen U := (isOpen_interior.inter E.open_source).inter hW
  have hpU : p ∈ U := ⟨⟨mem_interior_iff_mem_nhds.mpr hV,hpE⟩,hpW⟩
  have hsub : U ⊆ E.source := fun _ hx => hx.1.2
  have hinj : Set.InjOn (toCharacter i) U := by
    intro x hx y hy he
    obtain ⟨g,hg⟩ := (toCharacter_eq_iff i x y).mp he
    have hfix := hstab g ⟨x,⟨⟨y,interior_subset hy.1.1,hg⟩,interior_subset hx.1.1⟩⟩
    have hg1 := hfree g hfix
    simpa only [hg1,one_smul] using hg.symm
  let q := imageMap (toCharacter i) U
  let f := imageMap E U
  have hq : IsOpenQuotientMap q := imageMap_openQuotient _ U
    (toCharacter_continuous i).continuousOn
    ((toCharacter_open i).comp hU.isOpenMap_subtype_val)
  have hf : IsOpenQuotientMap f := imageMap_openQuotient E U
    (E.continuousOn.mono hsub) (restricted_chart_open E U hU hsub)
  have hrel : ∀ x y : U,q x = q y ↔ f x = f y := by
    intro x y
    constructor
    · intro he
      exact Subtype.ext (congrArg E (hinj x.property y.property (congrArg Subtype.val he)))
    · intro he
      exact Subtype.ext (congrArg (toCharacter i)
        (E.injOn (hsub x.property) (hsub y.property) (congrArg Subtype.val he)))
  let H := homeomorph q f hq.isQuotientMap hf.isQuotientMap hrel
  have hQ := toCharacter_open i U hU
  have hF := E.isOpen_image_of_subset_source hU hsub
  let hne : Nonempty (toCharacter i '' U) := ⟨⟨toCharacter i p,⟨p,hpU,rfl⟩⟩⟩
  let e := OpenImageHomeomorphChart318.extend _ _ hQ hF hne H
  refine ⟨U,e,hU,hpU,fun _ hx => hx.2,hsub,
    OpenImageHomeomorphChart318.extend_source _ _ hQ hF hne H,?_⟩
  intro x hx
  have hH := homeomorph_value q f hq.isQuotientMap hf.isQuotientMap hrel (⟨x,hx⟩ : U)
  have he := OpenImageHomeomorphChart318.extend_value _ _ hQ hF hne H
    (⟨toCharacter i x,⟨x,hx,rfl⟩⟩ : toCharacter i '' U)
  exact he.trans (congrArg Subtype.val hH)

/-- Actual local z² model of the SAME intermediate projection at EVERY
visible original inertia point. Both coordinate maps are genuine open
partial homeomorphisms on the actual quotients. The target chart is an old
maximal atlas chart; the source chart's original pullback is holomorphic.
No global intermediate complex atlas is assumed. -/
theorem visible_local_square (i : Fin 4) (j : Fin 5) (τ : HalfPlane)
    (hp : PELUnlevelledComplexBase318.projection τ ∈ fixedLocus j)
    (hvisible : InertiaLabels318.fiveLabels j i ≠ 0) :
    ∃ (U : Set UnlevelledBase)
      (e : OpenPartialHomeomorph (CharacterBase i) ℂ)
      (b : OpenPartialHomeomorph MaximalBase ℂ),
      IsOpen U ∧ PELUnlevelledComplexBase318.projection τ ∈ U ∧
      e.source = toCharacter i '' U ∧
      PELMaximalTopologicalAtlas318.OriginalChart b ∧
      e (toCharacter i (PELUnlevelledComplexBase318.projection τ)) = 0 ∧
      (∀ q ∈ e.source, toMaximal i q ∈ b.source ∧ b (toMaximal i q) = (e q)^2) ∧
      ∀ x ∈ U, ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
        (fun y => e (toCharacter i y)) x := by
  obtain ⟨W,b,hW,hpW,hbs,hbval,hbhol⟩ :=
    PELMaximalTopologicalAtlas318.exists_branch_chart j τ hp
  obtain ⟨U,e,hU,hpU,hUW,hUE,hes,heval⟩ := free_chart i
    (PELUnlevelledComplexBase318.projection τ) (inertiaChart τ)
    (chart_center_source τ) W hW hpW (visible_kernel_free i j _ hp hvisible)
  refine ⟨U,e,b,hU,hpU,hes,⟨W,hW,hbs,hbhol⟩,?_,?_,?_⟩
  · rw [heval _ hpU,chart_center]
  · intro q hq
    rw [hes] at hq
    obtain ⟨x,hx,rfl⟩ := hq
    constructor
    · rw [original_square,hbs]
      exact ⟨x,hUW hx,rfl⟩
    · rw [original_square,hbval _ (hUW hx),heval _ hx]
      rfl
  · intro x hx
    have hh := chart_holomorphic τ x (hUE hx)
    apply hh.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact heval y hy
end PELOriginalCharacterLocalSquare318
