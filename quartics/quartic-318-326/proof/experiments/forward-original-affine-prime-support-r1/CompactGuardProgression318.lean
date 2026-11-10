module
public import AnalyticGuardAvoidance318
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure
public import Mathlib.Data.Nat.ModEq
public section

/-! Compact-group recurrence and simultaneous guard selection in progressions.
This does not supply the actual elliptic orbit closure or its torus cover. -/
namespace CompactGuardProgression318
open Set Filter TopologicalSpace
open scoped Topology
set_option maxHeartbeats 1000000

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G]
  [IsTopologicalAddGroup G] [CompactSpace G]

/-- Every open set is met arbitrarily late by the positive orbit of a dense
cyclic subgroup. This is derived from compact recurrence, not assumed. -/
theorem positive_tail (a b : G) (hd : DenseRange (fun n : ℤ => n • a))
    (U : Set G) (ho : IsOpen U) (hne : U.Nonempty) (B : ℕ) :
    ∃ n : ℕ, B<n ∧ b+n • a∈U := by
  obtain ⟨x,hx⟩ := hne
  have hcl : x-b ∈ (AddSubgroup.zmultiples a).topologicalClosure := by
    change x-b ∈ closure (range (fun n : ℤ => n • a))
    exact hd (x-b)
  have hrec := mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples.mpr hcl
  have hnb : (fun y : G => b+y) ⁻¹' U ∈ 𝓝 (x-b) :=
    (ho.preimage (continuous_const.add continuous_id)).mem_nhds (by simpa [add_comm] using hx)
  exact frequently_atTop'.mp (hrec.frequently hnb) B

omit [CompactSpace G] in
/-- Surjective multiplication on a connected torus preserves dense cyclic
orbits. The surjectivity input is explicit; no connectedness theorem is hidden. -/
theorem dense_multiple (a : G) (hd : DenseRange (fun n : ℤ => n • a))
    (k : ℕ) (hk : Function.Surjective (fun x : G => k • x)) :
    DenseRange (fun n : ℤ => n • (k • a)) := by
  have hc : Continuous (fun x : G => k • x) := continuous_id.const_smul k
  have hh := hk.denseRange.comp hd hc
  simpa only [Function.comp_def,smul_comm k] using hh

omit [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] in
/-- Component annihilation passes to every allowed step multiple. -/
theorem component_step_mem (H : AddSubgroup G) (m k : ℕ) (hmk : m∣k)
    (hkill : ∀ x : G, m • x∈H) : ∀ x : G, k • x∈H := by
  obtain ⟨l,rfl⟩ := hmk
  intro x
  rw [Nat.mul_comm,mul_smul]
  exact H.nsmul_mem (hkill x) l

omit [CompactSpace G] in
/-- Exact component-aware density: the original generator need not belong
to the identity component. Its step does, by the displayed annihilation
hypothesis, and surjectivity of step multiplication on H gives dense image. -/
theorem dense_component_multiple (P : G) (hd : DenseRange (fun n : ℤ => n • P))
    (H : AddSubgroup G) (k : ℕ) (hmem : ∀ x : G, k • x∈H)
    (hs : Function.Surjective (fun x : H => k • x)) :
    DenseRange (fun n : ℤ => n • (⟨k • P,hmem P⟩ : H)) := by
  let f : G → H := fun x => ⟨k • x,hmem x⟩
  have hf : Continuous f := (continuous_id.const_smul k).subtype_mk _
  have hsf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hs y
    refine ⟨x.val,?_⟩
    exact hx
  have hh := hsf.denseRange.comp hd hf
  convert hh using 1
  funext n
  apply Subtype.ext
  change n • (k • P)=k • (n • P)
  exact smul_comm n k P

/-- The literal residue class is preserved at every positive-tail index. -/
theorem progression_modEq (d r k n : ℕ) (hk : d∣k) : Nat.ModEq d (r+k*n) r := by
  have hd : d∣k*n := dvd_mul_of_dvd_left hk n
  simp [Nat.ModEq,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [TopologicalSpace G] [IsTopologicalAddGroup G] [CompactSpace G] in
/-- A genuine surjective additive real cover supplies divisibility of the
torus group, so nonzero step multiplication need not be assumed separately. -/
theorem real_cover_multiplication_surjective (π : V →+ G) (hs : Function.Surjective π)
    (k : ℕ) (hk : k≠0) : Function.Surjective (fun x : G => k • x) := by
  intro y
  obtain ⟨v,hv⟩ := hs y
  refine ⟨π ((k:ℝ)⁻¹ • v),?_⟩
  change k • π ((k:ℝ)⁻¹ • v)=y
  rw [←map_nsmul]
  have he : k • ((k:ℝ)⁻¹ • v)=v := by
    rw [←Nat.cast_smul_eq_nsmul ℝ,smul_smul,
      mul_inv_cancel₀ (by exact_mod_cast hk : (k:ℝ)≠0),one_smul]
  rw [he,hv]

/-- One point meets all four guards, the scalar region and inherited poles,
while belonging to the chosen translated positive orbit beyond any bound. -/
theorem simultaneous_progression
    (π : V → G) (hπ : Continuous π) (hs : Function.Surjective π)
    (g : Fin 4 → G → ℝ) (hg : ∀ j : Fin 4, Continuous (g j))
    (ha : ∀ j : Fin 4, AnalyticOnNhd ℝ (g j ∘ π) univ)
    (hn : ∀ j : Fin 4, g j (π 0)≠0) (Ω A : Set G)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hA : IsOpen A) (hdA : Dense A)
    (a b : G) (hd : DenseRange (fun n : ℤ => n • a)) (B : ℕ) :
    ∃ n : ℕ, B<n ∧ b+n • a∈Ω ∧
      (∀ j : Fin 4, g j (b+n • a)≠0) ∧ b+n • a∈A := by
  obtain ⟨ho,he⟩ := AnalyticGuardAvoidance318.simultaneous_open π hπ hs g hg ha hn Ω A hΩ hne hA hdA
  obtain ⟨n,hBn,hgood⟩ := positive_tail a b hd _ ho he B
  exact ⟨n,hBn,hgood.1,hgood.2.1,hgood.2.2⟩

/-- The compact good region and guard lower bounds are chosen before any
progression step or translate. Subsequent dense progressions all meet it. -/
theorem compact_before_progressions
    (π : V → G) (hπ : Continuous π) (hs : Function.Surjective π)
    (g : Fin 4 → G → ℝ) (hg : ∀ j : Fin 4, Continuous (g j))
    (ha : ∀ j : Fin 4, AnalyticOnNhd ℝ (g j ∘ π) univ)
    (hn : ∀ j : Fin 4, g j (π 0)≠0) (Ω A : Set G)
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hA : IsOpen A) (hdA : Dense A) :
    ∃ K : PositiveCompacts G, ∃ ε : Fin 4 → ℝ,
      (K : Set G) ⊆ Ω ∩ (AnalyticGuardAvoidance318.good g ∩ A) ∧
      (∀ j : Fin 4, 0<ε j) ∧ (∀ j : Fin 4, ∀ x∈(K : Set G), ε j≤|g j x|) ∧
      ∀ a b : G, DenseRange (fun n : ℤ => n • a) → ∀ B : ℕ,
        ∃ n : ℕ, B<n ∧ b+n • a∈interior (K : Set G) := by
  obtain ⟨ho,he⟩ := AnalyticGuardAvoidance318.simultaneous_open π hπ hs g hg ha hn Ω A hΩ hne hA hdA
  obtain ⟨K,hK⟩ := AnalyticGuardAvoidance318.compact_guard_region g Ω A ho he
  obtain ⟨ε,hε,hbounds⟩ := AnalyticGuardAvoidance318.compact_uniform_bounds g hg K K.isCompact
    (fun _ hx => (hK hx).2.1)
  refine ⟨K,ε,hK,hε,hbounds,?_⟩
  intro a b hd B
  exact positive_tail a b hd _ isOpen_interior K.interior_nonempty B

end CompactGuardProgression318
