module
public import OriginalGoodCotangentLattice318
public section
noncomputable section
namespace OriginalSectionLatticeGeneration318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open OriginalGoodCotangentLattice318 FinitePlacePrincipalLattice318
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1) (i : Fin 4)

/-- The original two global J² section values generate the entire actual
integral cotangent-square lattice at each good place. This is equality of
embedded valuation-ring submodules, not just a maximum-norm identity. -/
theorem original_pair_span :
    Submodule.span (V c t v) {ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i}=modelLattice c t hn v hv i := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl|rfl
    · exact original_sections_mem c t hn v hv i 0
    · exact original_sections_mem c t hn v hv i 1
  · rcases one_original_section_generates c t hn v hv i with h|h
    · rw [h]
      exact lattice_le_of_mem v _ _ (Submodule.subset_span (Or.inl rfl))
    · rw [h]
      exact lattice_le_of_mem v _ _ (Submodule.subset_span (Or.inr rfl))
end OriginalSectionLatticeGeneration318
