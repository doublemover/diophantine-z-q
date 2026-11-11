/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
/- Port of official mathlib PR33505, head d43061d911b1aeae0788591da437a3b115098962.
Adapted for project isolation at pinned mathlib56a005855ea17e0b0958f73ec801ae140b0a1679.
Upstream helper names are suffixed318 to avoid collisions; proof content preserved initially.
This is an interior theorem only, not boundary extension or compact-curve uniformization. -/
module
public import RiemannNormalFamily318

public section
noncomputable section
open Set Metric Function Filter
open scoped Pointwise Topology ComplexConjugate Real BigOperators Uniformity
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

namespace Complex
theorem exists_branch_log318 {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X] {U : Set X}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : X → ℂ} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ EqOn (exp ∘ f) g U := by
  classical
  have := hUc.simplyConnectedSpace
  have := hUo.locallyPathConnectedSpace
  rcases hUc.nonempty with ⟨x₀, hx₀U⟩
  have hx₀ : g x₀ ≠ 0 := ne_of_mem_of_not_mem (mem_image_of_mem g hx₀U) hU₀
  lift x₀ to U using hx₀U
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨U.restrict g, continuousOn_iff_continuous_restrict.mp hgc⟩ (exp_log hx₀)
    (fun x ↦ ne_of_mem_of_not_mem (mem_image_of_mem g x.2) hU₀) with ⟨f, ⟨-, hf⟩, -⟩
  obtain ⟨g, hg⟩ : ∃ g : X → ℂ, ∀ z : U, g z = f z :=
    ⟨fun z ↦ if hz : z ∈ U then f ⟨z, hz⟩ else 0, by simp⟩
  refine ⟨g, ?hg_cont, ?hg_inv⟩
  case hg_cont =>
    rw [continuousOn_iff_continuous_restrict]
    convert map_continuous f
    ext z
    exact hg z
  case hg_inv =>
    intro x hx
    lift x to U using hx
    simpa only [Function.comp_apply, ContinuousMap.coe_mk, Set.restrict, Set.domRestrict, hg] using congrFun hf x

theorem exists_branch_nthRoot318 {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X] {U : Set X}
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : X → ℂ} (hgc : ContinuousOn g U)
    (hU₀ : 0 ∉ g '' U) {n : ℕ} (hn : n ≠ 0) :
    ∃ f : X → ℂ, ContinuousOn f U ∧ ∀ x, f x ^ n = g x := by
  classical
  rcases exists_branch_log318 hUc hUo hgc hU₀ with ⟨f, hfc, hf⟩
  refine ⟨U.piecewise (exp <| f · / n) (g · ^ (1 / n : ℂ)), ?_, fun z ↦ ?_⟩
  · rw [continuousOn_iff_continuous_restrict, restrict_piecewise,
      ← continuousOn_iff_continuous_restrict]
    fun_prop
  · by_cases hz : z ∈ U
    · simp [hz, ← exp_nat_mul, mul_div_cancel₀ (b := ↑n) (f z) (mod_cast hn), ← hf hz,
        Function.comp_apply]
    · simp [hz, ← cpow_mul_nat, hn]

namespace UnitDisc

protected theorem exists_branch_nthRoot318 {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X]
    {U : Set X} (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : X → UnitDisc}
    (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) (n : ℕ+) :
    ∃ f : X → UnitDisc, ContinuousOn f U ∧ ∀ x, f x ^ n = g x := by
  rcases exists_branch_nthRoot318 hUc hUo
    (continuous_coe.comp_continuousOn hgc)
    (by simpa using hU₀) n.ne_zero with ⟨f, hfc, hf⟩
  suffices ∀ x, ‖f x‖ < 1 by
    lift f to X → 𝔻 using this
    refine ⟨f, isEmbedding_coe.continuousOn_iff.mpr hfc, fun x ↦ ?_⟩
    simpa only [← coe_pow, Function.comp_apply, coe_inj] using hf x
  intro x
  rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) n.ne_zero, ← norm_pow, hf]
  exact (g x).norm_lt_one

@[fun_prop]
theorem continuous_shift318 (z : 𝔻) : Continuous z.shift := by
  simp only [isEmbedding_coe.continuous_iff, Function.comp_def, coe_shift]
  exact .div (by fun_prop) (by fun_prop) fun _ ↦ shift_den_ne_zero _ _

end UnitDisc

theorem exists_mapsTo_unitBall_injOn_deriv_ne_zero318 {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) {x : ℂ} (hx : x ∈ U) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU]) (x := -a + x)
      (by simpa [mem_vadd_set_iff_neg_vadd_mem]) (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf₁, hf_inj, hdf⟩
    refine ⟨f ∘ (-a + ·), hf₁.comp (mapsTo_image _ _),
      hf_inj.comp (by simp [InjOn]) (mapsTo_image _ _), fun z hz ↦ ?_⟩
    simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)
  rcases exists_branch_nthRoot318 hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  have hdf' : DifferentiableOn ℂ f U := fun z hz ↦
    (hdf z hz).hasDerivAt.differentiableAt.differentiableWithinAt
  have hfUx : f '' U ∈ 𝓝 (f x) := by
    rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
    exact Filter.image_mem_map <| hUo.mem_nhds hx
  have hdisj : ∀ a ∈ U, ∀ b ∈ U, f a + f b ≠ 0 := by
    intro a ha b hb hfab
    obtain rfl : b = a := by
      rw [← hf_inv a, ← hf_inv b]
      simp [eq_neg_iff_add_eq_zero.mpr hfab]
    have : f b = 0 := by linear_combination hfab / 2
    exact hf₀ b hb this
  have hfUxc : (f '' U)ᶜ ∈ 𝓝 (-f x) := by
    rw [nhds_neg, Filter.mem_neg]
    filter_upwards [hfUx]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    exact hdisj a ha b hb (by linear_combination hab)
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hfUxc with ⟨ε, hε₀, hε⟩
  use fun z ↦ ε / (f x + f z)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · by_contra! hle
      refine @hε (f z) ?_ (mem_image_of_mem f hz)
      simpa [dist_eq_norm, add_comm] using hle
    · simpa using hdisj x hx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inv.injective.eq_iff] using heq
  case deriv =>
    intro z hz
    rw [(hasDerivAt_const _ _).fun_div ((hdf z hz).hasDerivAt.const_add _) _ |>.deriv]
    · simp [hε₀.ne', hf₀ z hz, hdisj x hx z hz]
    · exact hdisj x hx z hz

theorem UnitDisc.hasDerivWithinAt_shift_comp318 {f : ℂ → UnitDisc} {z f' : ℂ} {s : Set ℂ}
    (w : UnitDisc) (hf : HasDerivWithinAt (fun x ↦ ↑(f x)) f' s z) :
    HasDerivWithinAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') s z := by
  simp only [coe_shift]
  convert (hf.const_add _).fun_div ((hf.const_mul _).const_add _) _ using 1
  · rw [← mul_conj']
    ring
  · apply UnitDisc.shift_den_ne_zero

theorem UnitDisc.hasDerivAt_shift_comp318 {f : ℂ → UnitDisc} {z f' : ℂ} (w : UnitDisc)
    (hf : HasDerivAt (fun x ↦ ↑(f x)) f' z) :
    HasDerivAt (fun x ↦ w.shift (f x) : ℂ → ℂ)
      ((1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * f') z :=
  (hasDerivWithinAt_shift_comp318 w hf.hasDerivWithinAt).hasDerivAt univ_mem

@[simp]
theorem UnitDisc.differentiableWithinAt_shift_comp_iff318 {f : ℂ → UnitDisc} {z : ℂ} {s : Set ℂ}
    (w : UnitDisc) :
    DifferentiableWithinAt ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) s z ↔
      DifferentiableWithinAt ℂ (f · : ℂ → ℂ) s z := by
  refine ⟨fun h ↦ ?_, fun h ↦
    (hasDerivWithinAt_shift_comp318 w h.hasDerivWithinAt).differentiableWithinAt⟩
  simpa using (hasDerivWithinAt_shift_comp318 (-w) h.hasDerivWithinAt).differentiableWithinAt

@[simp]
theorem UnitDisc.differentiableOn_shift_comp_iff318 {f : ℂ → UnitDisc} {s : Set ℂ} (w : UnitDisc) :
    DifferentiableOn ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) s ↔
      DifferentiableOn ℂ (f · : ℂ → ℂ) s := by
  simp [DifferentiableOn]

@[simp]
theorem UnitDisc.differentiableAt_shift_comp_iff318 {f : ℂ → UnitDisc} {z : ℂ} (w : UnitDisc) :
    DifferentiableAt ℂ (fun x ↦ w.shift (f x) : ℂ → ℂ) z ↔
      DifferentiableAt ℂ (f · : ℂ → ℂ) z := by
  refine ⟨fun h ↦ ?_, fun h ↦ (hasDerivAt_shift_comp318 w h.hasDerivAt).differentiableAt⟩
  simpa using (hasDerivAt_shift_comp318 (-w) h.hasDerivAt).differentiableAt

@[simp]
theorem UnitDisc.deriv_shift_comp318 (f : ℂ → UnitDisc) (z : ℂ) (w : UnitDisc) :
    deriv (fun x ↦ w.shift (f x) : ℂ → ℂ) z =
      (1 - ‖(w : ℂ)‖ ^ 2) / (1 + conj ↑w * f z) ^ 2 * deriv (f · : ℂ → ℂ) z := by
  by_cases hfd : DifferentiableAt ℂ (f · : ℂ → ℂ) z
  · exact (hasDerivAt_shift_comp318 w hfd.hasDerivAt).deriv
  · rw [deriv_zero_of_not_differentiableAt hfd, deriv_zero_of_not_differentiableAt, mul_zero]
    simpa using hfd

theorem UnitDisc.deriv_shift_comp_eq_zero318 (f : ℂ → UnitDisc) (z : ℂ) (w : UnitDisc) :
    deriv (fun x ↦ w.shift (f x) : ℂ → ℂ) z = 0 ↔ deriv (f · : ℂ → ℂ) z = 0 := by
  simp only [deriv_shift_comp318, mul_eq_zero, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero,
    shift_den_ne_zero, or_false]
  apply or_iff_right
  exact mod_cast sub_ne_zero.mpr w.sq_norm_lt_one.ne'


end Complex
