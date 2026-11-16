module
public import FinitePlacePrincipalImage318
public section
noncomputable section
namespace FinitePlaceTwoSectionLattice318
open NumberField ActualFinitePlaceIntegers318 FinitePlacePrincipalLattice318
variable {K : Type*} [Field K] [NumberField K]
variable (v : FinitePlace K) (a b : K)

/-- Choose one of the actual section values, not a new geometric frame.
Its valuation is the maximum of the two section valuations. -/
@[expose] def generator : K := if v b ≤ v a then a else b

theorem generator_value : v (generator v a b) = max (v a) (v b) := by
  unfold generator
  split_ifs with h
  · exact (max_eq_left h).symm
  · exact (max_eq_right (le_of_not_ge h)).symm

theorem generator_ne (ha : a ≠ 0) : generator v a b ≠ 0 := by
  intro h
  have hpos : 0 < v (generator v a b) := by
    rw [generator_value]
    exact lt_of_lt_of_le (v.pos ha) (le_max_left _ _)
  rw [h, map_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- A nonzero principal local lattice contains exactly the elements whose
valuation is at most the valuation of its generator. -/
theorem mem_iff_le (g x : K) (hg : g ≠ 0) :
    x ∈ lattice v g ↔ v x ≤ v g := by
  rw [mem_iff_norm v g hg]
  change v x / v g ≤ 1 ↔ v x ≤ v g
  rw [div_le_iff₀ (v.pos hg), one_mul]

@[expose] def sectionLattice : Submodule (Integers v) K :=
  lattice v (generator v a b)

theorem left_mem (ha : a ≠ 0) : a ∈ sectionLattice v a b := by
  apply (mem_iff_le v _ _ (generator_ne v a b ha)).mpr
  rw [generator_value]
  exact le_max_left _ _

theorem right_mem (ha : a ≠ 0) : b ∈ sectionLattice v a b := by
  apply (mem_iff_le v _ _ (generator_ne v a b ha)).mpr
  rw [generator_value]
  exact le_max_right _ _

/-- Universal minimality among actual embedded integral submodules.
No freeness or principal-generation premise on M is needed. -/
theorem minimal (M : Submodule (Integers v) K) (ha : a ∈ M) (hb : b ∈ M) :
    sectionLattice v a b ≤ M := by
  apply lattice_le_of_mem
  unfold generator
  split_ifs
  · exact ha
  · exact hb

theorem le_iff (ha : a ≠ 0) (M : Submodule (Integers v) K) :
    sectionLattice v a b ≤ M ↔ a ∈ M ∧ b ∈ M :=
  ⟨fun h => ⟨h (left_mem v a b ha), h (right_mem v a b ha)⟩,
    fun h => minimal v a b M h.1 h.2⟩

/-- The construction is intrinsically the span of the two original values;
the tie-breaking generator is not part of its mathematical meaning. -/
theorem eq_span (ha : a ≠ 0) :
    sectionLattice v a b = Submodule.span (Integers v) ({a,b} : Set K) := by
  apply le_antisymm
  · apply minimal
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact left_mem v a b ha
    · exact right_mem v a b ha

/-- Explicit local norm. This is the norm of the minimal section lattice,
not an assertion that it is a cotangent or Hodge lattice. -/
theorem inverse_generator_value :
    (v (generator v a b))⁻¹ = (max (v a) (v b))⁻¹ := by
  rw [generator_value]
/-- Exact covariance under a genuine nonzero change of rational frame.
The local generator is transported, not replaced by an abstract basis. -/
theorem generator_scale (k : K) (hk : k ≠ 0) :
    generator v (k*a) (k*b) = k * generator v a b := by
  unfold generator
  rw [map_mul, map_mul, mul_le_mul_left (v.pos hk)]
  split_ifs <;> rfl

theorem lattice_scale (k : K) (hk : k ≠ 0) :
    sectionLattice v (k*a) (k*b) =
      (sectionLattice v a b).map (FinitePlacePrincipalImage318.scalarMap v k) := by
  unfold sectionLattice
  rw [generator_scale v a b k hk, FinitePlacePrincipalImage318.scalar_image]

end FinitePlaceTwoSectionLattice318
