module
public import PELOriginalPeriodLattice318
public import PELComplexPeriodSurface318
public section
noncomputable section
namespace PELOriginalPeriodIntegerCoordinates318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalPeriodLattice318 PELComplexPeriodSurface318
variable (τ : ℂ) (hτ : 0 < τ.im)
/-- Membership in the ENTIRE original period subgroup is exactly
membership in the integer coordinate lattice of the computed real
basis. Original order denominators and the actual embedding are retained. -/
lemma mem_iff (z : ComplexVectors) : z∈Periods τ ↔
    ∃ a : Fin 4 → ℤ,z=coordinates τ hτ (fun i => (a i : ℝ)) := by
  constructor
  · rintro ⟨x,hx,hz⟩
    obtain ⟨a,rfl⟩ := hx
    exact ⟨a,hz.symm.trans (original_coordinates τ hτ a)⟩
  · rintro ⟨a,rfl⟩
    rw [←original_coordinates τ hτ a]
    exact ⟨embed a,⟨a,rfl⟩,rfl⟩
lemma coordinates_mem (a : Fin 4 → ℤ) :
    coordinates τ hτ (fun i => (a i : ℝ))∈Periods τ := (mem_iff τ hτ _).mpr ⟨a,rfl⟩
end PELOriginalPeriodIntegerCoordinates318
