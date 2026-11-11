module
public import CompactComplexPeriodSpan318
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public section
noncomputable section
namespace CompactComplexRankTwoPeriods318
open Set Module
set_option maxHeartbeats 2200000
variable (L : AddSubgroup ℂ) [DiscreteTopology L]
variable [CompactSpace (ComplexAffineFreeTranslation318.Torus L)]

/-- The SAME actual additive period subgroup viewed as its canonical
integer submodule; the underlying subtype and topology are unchanged. -/
@[expose] def integerModule : Submodule ℤ ℂ where
  carrier := L
  zero_mem' := L.zero_mem
  add_mem' := L.add_mem
  smul_mem' n z hz := L.zsmul_mem hz n

local instance : DiscreteTopology (integerModule L) := by
  change DiscreteTopology L
  infer_instance
local instance : IsZLattice ℝ (integerModule L) :=
  ⟨CompactComplexPeriodSpan318.real_span_top L⟩

/-- Rank two follows from discreteness and compactness of the ACTUAL
quotient, via real span and the lattice rank theorem. -/
theorem rank_two : Module.finrank ℤ (integerModule L)=2 := by
  rw [ZLattice.rank ℝ (integerModule L),Complex.finrank_real_complex]

@[expose] def integerBasis : Basis (Fin 2) ℤ (integerModule L) :=
  Module.finBasisOfFinrankEq ℤ (integerModule L) (rank_two L)

/-- Actual integer coordinates for all periods, not two chosen periods
without a spanning proof. -/
@[expose] def coordinates : RankTwoComplexHalfPeriods318.Coordinates ≃+ L :=
  (integerBasis L).equivFun.toAddEquiv.symm
end CompactComplexRankTwoPeriods318
