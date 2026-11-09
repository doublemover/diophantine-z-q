module
public import ActualFiveDifferentialSpanning318
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite

public section
noncomputable section
namespace ActualFiveDifferentialBasis318
open AlgebraicGeometry SourceTwistArithmetic318
open ActualFiveRationalIndependent318
open scoped BigOperators
attribute [local instance] rationalModule
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem span_eq_top : Submodule.span ℚ (Set.range differential) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨a, b, hs⟩ := ActualFiveDifferentialSpanning318.exists_coefficients s
  rw [hs]
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨some i, rfl⟩)
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩)

/-- A basis of the genuine global intrinsic differential space of the
original complete source. Its entries are the five actual elliptic
pullbacks, using the unchanged structural rational action. -/
@[expose] def basis : Module.Basis (Option (Fin 4)) ℚ G :=
  Module.Basis.mk independent span_eq_top.ge

theorem basis_apply (i : Option (Fin 4)) : basis i = differential i := by
  exact Module.Basis.mk_apply _ _ i

theorem finrank_eq_five : Module.finrank ℚ G = 5 := by
  rw [Module.finrank_eq_card_basis basis]
  decide

end ActualFiveDifferentialBasis318
