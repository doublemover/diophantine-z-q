module
public import AffineCoverHOneQuotient318
public import ActualSourceHOnePresentation318
public section
noncomputable section
namespace ActualSourceHOneQuotient318
open AlgebraicGeometry ActualSourceHOnePresentation318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance sourceIntegral : IsIntegral Source := ContactProjectiveModel318.model_integral SourceTwistArithmetic318.units
abbrev difference := AffineCoverHOneQuotient318.difference finiteOpen infinityOpen

/-- The actual finite/infinity restriction quotient is the unchanged source H1. -/
@[expose] def equivalence : Γ(Source,finiteOpen ⊓ infinityOpen) ⧸ difference.range ≃+
    ActualSourceHOnePullbacks318.SourceHOne :=
  AffineCoverHOneQuotient318.equivalence finiteOpen infinityOpen finite_affine infinity_affine cover

theorem equivalence_mk (x : Γ(Source,finiteOpen ⊓ infinityOpen)) :
    equivalence (QuotientAddGroup.mk x) = ActualSourceHOnePresentation318.boundary x := rfl

/-- Zero classes are exactly the original finite/infinity restriction differences. -/
theorem boundary_eq_zero_iff_mem_range (x : Γ(Source,finiteOpen ⊓ infinityOpen)) :
    ActualSourceHOnePresentation318.boundary x = 0 ↔ x ∈ difference.range := by
  change x ∈ (AffineCoverHOnePresentation318.boundary finiteOpen infinityOpen cover).ker ↔ _
  rw [AffineCoverHOneQuotient318.kernel_eq_range]

/-- Equality in actual source H1 is exactly equality modulo the original restrictions. -/
theorem boundary_eq_iff (x y : Γ(Source,finiteOpen ⊓ infinityOpen)) :
    ActualSourceHOnePresentation318.boundary x = ActualSourceHOnePresentation318.boundary y ↔
      x - y ∈ difference.range := by
  rw [← sub_eq_zero, ← map_sub]
  exact boundary_eq_zero_iff_mem_range (x-y)

end ActualSourceHOneQuotient318
