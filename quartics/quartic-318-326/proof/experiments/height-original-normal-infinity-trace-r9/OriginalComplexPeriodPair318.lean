module
public import PELOriginalUniformizationOnly318
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public section
noncomputable section
namespace OriginalComplexPeriodPair318
open CompactComplexRankTwoPeriods318 Module Set
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L]
variable [CompactSpace (ComplexAffineFreeTranslation318.Torus L)]

local instance : DiscreteTopology (integerModule L) := by
  change DiscreteTopology L
  infer_instance
local instance : IsZLattice ℝ (integerModule L) :=
  ⟨CompactComplexPeriodSpan318.real_span_top L⟩

/-- The actual integer period basis also spans C over R, by the proved
full-lattice comparison, not an assumed independent pair. -/
@[expose] def realBasis : Basis (Fin 2) ℝ ℂ :=
  (integerBasis L).ofZLatticeBasis ℝ

@[expose] def pair : PeriodPair where
  ω₁ := realBasis L 0
  ω₂ := realBasis L 1
  indep := by
    convert (realBasis L).linearIndependent using 1
    funext j
    fin_cases j <;> rfl

/-- The library's actual Weierstrass lattice is exactly ALL of the
original periods. No finite-index replacement lattice is introduced. -/
theorem pair_lattice : (pair L).lattice=integerModule L := by
  have hr : range (realBasis L)={realBasis L 0,realBasis L 1} := by
    ext z
    constructor
    · rintro ⟨j,rfl⟩
      fin_cases j <;> simp
    · intro hz
      rcases hz with hz | hz
      · exact ⟨0,hz.symm⟩
      · exact ⟨1,hz.symm⟩
  change Submodule.span ℤ {realBasis L 0,realBasis L 1}=integerModule L
  rw [←hr]
  exact (integerBasis L).ofZLatticeBasis_span ℝ

theorem pair_mem (z : ℂ) : z∈(pair L).lattice ↔ z∈L := by
  rw [pair_lattice]
  rfl
end OriginalComplexPeriodPair318
