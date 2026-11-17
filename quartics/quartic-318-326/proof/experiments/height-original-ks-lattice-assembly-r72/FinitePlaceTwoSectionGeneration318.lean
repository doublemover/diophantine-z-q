module
public import FinitePlaceTwoSectionLattice318
public section
noncomputable section
namespace FinitePlaceTwoSectionGeneration318
open NumberField ActualFinitePlaceIntegers318 FinitePlacePrincipalLattice318
open FinitePlaceTwoSectionLattice318
variable {K : Type*} [Field K] [NumberField K]
variable (v : FinitePlace K) (a b g : K) (ha : a ≠ 0) (hg : g ≠ 0)

/-- Equality of embedded principal lattices is equivalent to equality of the
actual generator norms. No rank-one isomorphism is used. -/
theorem eq_iff_max : sectionLattice v a b = lattice v g ↔
    max (v a) (v b) = v g := by
  constructor
  · intro h
    have hleft : a ∈ lattice v g := h ▸ left_mem v a b ha
    have hright : b ∈ lattice v g := h ▸ right_mem v a b ha
    have hgen : g ∈ lattice v g := (mem_iff v g g).mpr ⟨1, by simp⟩
    have hback : g ∈ sectionLattice v a b := h.symm ▸ hgen
    apply le_antisymm
    · exact max_le ((mem_iff_le v g a hg).mp hleft)
        ((mem_iff_le v g b hg).mp hright)
    · have hb := (mem_iff_le v (generator v a b) g
          (generator_ne v a b ha)).mp hback
      simpa only [generator_value] using hb
  · intro h
    exact eq_of_norm v (generator v a b) g (generator_ne v a b ha) hg
      ((generator_value v a b).trans h)

/-- For a candidate lattice containing both original sections, the missing
reverse inclusion is exactly integrality of its own generator in their span. -/
theorem eq_iff_generator_mem (hleft : a ∈ lattice v g)
    (hright : b ∈ lattice v g) :
    sectionLattice v a b = lattice v g ↔ g ∈ sectionLattice v a b := by
  constructor
  · intro h
    rw [h]
    exact (mem_iff v g g).mpr ⟨1, by simp⟩
  · intro h
    exact le_antisymm (minimal v a b _ hleft hright) (lattice_le_of_mem v g _ h)

end FinitePlaceTwoSectionGeneration318
