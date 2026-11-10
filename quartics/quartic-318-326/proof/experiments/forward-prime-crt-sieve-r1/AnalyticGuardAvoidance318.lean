module
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic
public section

/-! Analytic zero avoidance through an explicit real covering space.
The actual elliptic orbit torus and its analytic covering map are not
constructed here. Every requirement on them is a displayed hypothesis. -/
namespace AnalyticGuardAvoidance318
open Set Filter TopologicalSpace
open scoped Topology
set_option maxHeartbeats 1000000

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Real analytic uniqueness in any normed dimension gives dense nonzero values.
No independence of two real embeddings and no one-dimensional zero theorem is used. -/
theorem analytic_nonzero_dense (f : V → ℝ) (hf : AnalyticOnNhd ℝ f univ)
    (hf0 : f 0≠0) : Dense {x | f x≠0} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  by_contra hbad
  have hz : ∀ x∈U, f x=0 := by
    intro x hx
    by_contra hn
    exact hbad ⟨x,hx,hn⟩
  obtain ⟨x,hx⟩ := hne
  have he : f=ᶠ[𝓝 x] 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hz y hy
  have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ x) he
  exact hf0 (hall (mem_univ 0))

variable {G : Type*} [TopologicalSpace G]

/-- A continuous surjective real covering suffices to descend zero avoidance.
The cover need not be injective; the orbit dimension is not fixed. -/
theorem covering_nonzero_dense (π : V → G) (hπ : Continuous π)
    (hs : Function.Surjective π) (g : G → ℝ)
    (ha : AnalyticOnNhd ℝ (g ∘ π) univ) (hn : g (π 0)≠0) :
    Dense {x | g x≠0} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨y,hy⟩ := hne
  obtain ⟨x,hx⟩ := hs y
  have hpre : (π ⁻¹' U).Nonempty := ⟨x,by simpa [hx] using hy⟩
  obtain ⟨z,hzU,hzg⟩ := (analytic_nonzero_dense (g ∘ π) ha hn).inter_open_nonempty
    (π ⁻¹' U) (hπ.isOpen_preimage U hU) hpre
  exact ⟨π z,hzU,hzg⟩

@[expose] def good (g : Fin 4 → G → ℝ) : Set G := {x | ∀ j : Fin 4, g j x≠0}

omit [TopologicalSpace G] in
theorem good_eq (g : Fin 4 → G → ℝ) :
    good g=(({x | g 0 x≠0} ∩ {x | g 1 x≠0}) ∩ {x | g 2 x≠0}) ∩ {x | g 3 x≠0} := by
  ext x
  simp only [good,mem_ofPred_eq,mem_inter_iff]
  constructor
  · intro h
    exact ⟨⟨⟨h 0,h 1⟩,h 2⟩,h 3⟩
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩ j
    fin_cases j <;> assumption

theorem good_open (g : Fin 4 → G → ℝ) (hg : ∀ j : Fin 4, Continuous (g j)) :
    IsOpen (good g) := by
  rw [good_eq]
  exact (((isOpen_ne.preimage (hg 0)).inter
    (isOpen_ne.preimage (hg 1))).inter
    (isOpen_ne.preimage (hg 2))).inter
    (isOpen_ne.preimage (hg 3))

/-- All four guards can be avoided at once, rather than selecting four points. -/
theorem good_dense (π : V → G) (hπ : Continuous π) (hs : Function.Surjective π)
    (g : Fin 4 → G → ℝ) (hg : ∀ j : Fin 4, Continuous (g j))
    (ha : ∀ j : Fin 4, AnalyticOnNhd ℝ (g j ∘ π) univ)
    (hn : ∀ j : Fin 4, g j (π 0)≠0) : Dense (good g) := by
  have hd (j : Fin 4) := covering_nonzero_dense π hπ hs (g j) (ha j) (hn j)
  rw [good_eq]
  exact (((hd 0).inter_of_isOpen_right (hd 1) (isOpen_ne.preimage (hg 1))).inter_of_isOpen_right
    (hd 2) (isOpen_ne.preimage (hg 2))).inter_of_isOpen_right
    (hd 3) (isOpen_ne.preimage (hg 3))

/-- Avoid all guards together with an inherited open dense pole-free set,
inside any prescribed nonempty open scalar region. -/
theorem simultaneous_open (π : V → G) (hπ : Continuous π) (hs : Function.Surjective π)
    (g : Fin 4 → G → ℝ) (hg : ∀ j : Fin 4, Continuous (g j))
    (ha : ∀ j : Fin 4, AnalyticOnNhd ℝ (g j ∘ π) univ)
    (hn : ∀ j : Fin 4, g j (π 0)≠0) (Ω A : Set G)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hA : IsOpen A) (hdA : Dense A) :
    IsOpen (Ω ∩ (good g ∩ A)) ∧ (Ω ∩ (good g ∩ A)).Nonempty := by
  exact ⟨hΩ.inter ((good_open g hg).inter hA),
    ((good_dense π hπ hs g hg ha hn).inter_of_isOpen_right hdA hA).inter_open_nonempty Ω hΩ hne⟩

/-- A compact set with nonempty interior can be fixed before progression moduli.
Its actual selection uses only the open set obtained above. -/
theorem compact_guard_region [LocallyCompactSpace G]
    (g : Fin 4 → G → ℝ) (Ω A : Set G)
    (ho : IsOpen (Ω ∩ (good g ∩ A))) (hne : (Ω ∩ (good g ∩ A)).Nonempty) :
    ∃ K : PositiveCompacts G, (K : Set G) ⊆ Ω ∩ (good g ∩ A) :=
  exists_positiveCompacts_subset ho hne

/-- Every guard has a uniform positive lower bound on any chosen compact region.
The bound may depend on the fixed labels and region, as in the source argument. -/
theorem compact_uniform_bounds (g : Fin 4 → G → ℝ)
    (hg : ∀ j : Fin 4, Continuous (g j)) (K : Set G) (hK : IsCompact K)
    (hne : K ⊆ good g) :
    ∃ ε : Fin 4 → ℝ, (∀ j : Fin 4, 0<ε j) ∧
      ∀ j : Fin 4, ∀ x∈K, ε j≤|g j x| := by
  have hmin (j : Fin 4) : ∃ e : ℝ, 0<e ∧ ∀ x∈K, e≤|g j x| :=
    hK.exists_forall_le' (hg j).abs.continuousOn (fun x hx => abs_pos.mpr (hne hx j))
  choose ε he hb using hmin
  exact ⟨ε,he,hb⟩

end AnalyticGuardAvoidance318
