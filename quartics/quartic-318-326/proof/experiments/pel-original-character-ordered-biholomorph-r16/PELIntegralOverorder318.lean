module
public import PELTraceDualSaturation318
public section
noncomputable section
namespace PELIntegralOverorder318
open PELQuaternionAlgebra318 PELPrincipalOrderCoordinates318 PELPrincipalOrderPerfect318
open PELTraceDualSaturation318
set_option maxHeartbeats 1000000

/-- The exact order itself has integral reduced trace and norm. -/
theorem order_trace_integral (x : B) (hx : x∈order) : ∃ z : ℤ,reducedTrace x=(z:ℚ) := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨2*a 0+a 2,?_⟩
  simp [reducedTrace,embed] <;> push_cast <;> ring

theorem order_norm_integral (x : B) (hx : x∈order) : ∃ z : ℤ,reducedNorm x=(z:ℚ) := by
  obtain ⟨a,rfl⟩ := hx
  refine ⟨a 0^2+a 0*a 2+210*a 1^2+210*a 1*a 3-a 2^2+42*a 3^2,?_⟩
  simp [reducedNorm,embed] <;> push_cast <;> ring

/-- There is no larger subring containing this order with integral reduced
trace and norm. This proves the concrete overorder obstruction; identifying
all module-finite Z-orders with these hypotheses remains a separate bridge. -/
theorem no_larger_integral_overorder (S : Subring B) (hOS : order≤S)
    (htrace : ∀ x∈S,∃ z : ℤ,reducedTrace x=(z:ℚ))
    (hnorm : ∀ x∈S,∃ z : ℤ,reducedNorm x=(z:ℚ)) : S=order := by
  apply le_antisymm _ hOS
  intro x hx
  apply mem_of_integral_trace_norm x
  · intro i
    exact htrace (x*embed (basis i))
      (S.mul_mem hx (hOS (show embed (basis i)∈order from ⟨basis i,rfl⟩)))
  · exact hnorm x hx
end PELIntegralOverorder318
