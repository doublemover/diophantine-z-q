module
public import CompactGuardProgression318
public import RealGuardTrace318
public section

/-! Conditional real-orbit selection for the actual rational guard values.
The actual orbit topology, analytic cover, scalar region and point comparison
are explicit inputs. Nonzero guard values at selected indices are conclusions. -/
namespace ActualGuardSelection318
open Set TopologicalSpace
open LocalGenerator318 (P)
set_option maxHeartbeats 1000000

variable {G V : Type*} [AddCommGroup G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [CompactSpace G]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] [NormedSpace ℝ V] in
/-- The actual positivity theorem supplies every cover nontriviality input. -/
theorem cover_nonzero (π : V → G) (g : Fin 4 → G → ℝ) (labels : Fin 4 → ℤ)
    (hn : ∀ j : Fin 4, labels j≠0)
    (h0 : ∀ j : Fin 4, g j (π 0)=(RealGuardTrace318.guardValue (labels j) 0 : ℝ)) :
    ∀ j : Fin 4, g j (π 0)≠0 := by
  intro j
  rw [h0 j]
  exact_mod_cast ne_of_gt (RealGuardTrace318.guard_at_identity_positive (labels j) (hn j))

/-- A single arbitrarily large permitted index has all four actual rational
trace guards nonzero, and its actual H is nonzero. Scalar-region and inherited
pole-free membership are retained at the same orbit point. -/
theorem select_actual_guards
    (π : V → G) (hπ : Continuous π) (hs : Function.Surjective π)
    (g : Fin 4 → G → ℝ) (hg : ∀ j : Fin 4, Continuous (g j))
    (ha : ∀ j : Fin 4, AnalyticOnNhd ℝ (g j ∘ π) univ)
    (labels : Fin 4 → ℤ) (hn : ∀ j : Fin 4, labels j≠0)
    (h0 : ∀ j : Fin 4, g j (π 0)=(RealGuardTrace318.guardValue (labels j) 0 : ℝ))
    (Ω A : Set G) (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hA : IsOpen A) (hdA : Dense A)
    (a b : G) (hd : DenseRange (fun n : ℤ => n • a))
    (r k : ℕ) (hk : 0<k)
    (hcompare : ∀ t : ℕ, ∀ j : Fin 4, g j (b+t • a)=
      (RealGuardTrace318.guardValue (labels j) (((r+k*t : ℕ):ℤ) • P) : ℝ)) (B : ℕ) :
    ∃ t : ℕ, B<r+k*t ∧ b+t • a∈Ω ∧ b+t • a∈A ∧
      (((r+k*t : ℕ):ℤ) • P)≠0 ∧
      ∀ j : Fin 4, RealGuardTrace318.guardValue (labels j) (((r+k*t : ℕ):ℤ) • P)≠0 := by
  obtain ⟨t,hBt,hΩt,hgt,hAt⟩ := CompactGuardProgression318.simultaneous_progression
    π hπ hs g hg ha (cover_nonzero π g labels hn h0) Ω A hΩ hne hA hdA a b hd B
  have hkt : t≤k*t := by nlinarith
  have hbig : B<r+k*t := by omega
  have hindex : ((r+k*t : ℕ):ℤ)≠0 := by
    exact_mod_cast (show r+k*t≠0 by omega)
  refine ⟨t,hbig,hΩt,hAt,RealMultiples318.multiple_P_nonzero _ hindex,?_⟩
  intro j
  have he := hgt j
  rw [hcompare t j] at he
  exact_mod_cast he

end ActualGuardSelection318
