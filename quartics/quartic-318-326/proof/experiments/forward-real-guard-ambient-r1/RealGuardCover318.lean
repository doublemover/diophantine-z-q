module
public import RealGuardAmbient318
public import AnalyticGuardAvoidance318
public section
noncomputable section
namespace RealGuardCover318
open Set RealQuarticAmbient318 RealGuardAmbient318
set_option maxHeartbeats 1000000
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The remaining analytic geometry input is an actual analytic surjection
onto the chosen source subset. The guard functions themselves are constructed. -/
theorem good_dense_of_analytic_cover (n : Fin 4 → ℤ) (hn : ∀ j, n j≠0)
    (S : Set Ambient) (π : V → S) (hs : Function.Surjective π)
    (ha : AnalyticOnNhd ℝ (fun x => (π x).val) univ)
    (h0 : (π 0).val=orbit n 0) :
    Dense {z : S | ∀ j : Fin 4, guard j z.val≠0} := by
  have hc : Continuous π := continuous_induced_rng.mpr (continuousOn_univ.mp ha.continuousOn)
  apply AnalyticGuardAvoidance318.good_dense π hc hs
    (fun j z => guard j z.val) (fun j => (guard_continuous j).comp continuous_subtype_val)
  · intro j x _
    exact (guard_analytic j _ (mem_univ _)).comp (ha x (mem_univ x))
  · intro j
    rw [h0]
    exact ne_of_gt (identity_guard_positive n j (hn j))

/-- Once the actual source component has its analytic cover, every nonempty
open scalar region meets all four actual nonzero guards simultaneously. The
cover and nonempty scalar region are explicit inputs, not asserted here. -/
theorem simultaneous_scalar_region (n : Fin 4 → ℤ) (hn : ∀ j, n j≠0)
    (S : Set Ambient) (π : V → S) (hs : Function.Surjective π)
    (ha : AnalyticOnNhd ℝ (fun x => (π x).val) univ)
    (h0 : (π 0).val=orbit n 0)
    (Ω : Set S) (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ z∈Ω, ∀ j : Fin 4, guard j z.val≠0 := by
  exact (good_dense_of_analytic_cover n hn S π hs ha h0).inter_open_nonempty Ω hΩ hne

end RealGuardCover318
