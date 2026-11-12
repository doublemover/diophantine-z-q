module
public import ActualTwoDescentFiniteCharacterFactor318
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public section
noncomputable section
namespace ActualTwoDescentFiniteCharacterHilbert318
set_option maxHeartbeats 16000000

open ActualTwoDescentSquareOneUnits318
variable {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]

/-- Genuine finite Hilbert90: the actual sign character is a multiplicative coboundary. -/
theorem actual_finite_character_hilbert (ψ : (L ≃ₐ[ℚ] L) →* SquareOne L) :
    ∃ b : Lˣ, ∀ σ : L ≃ₐ[ℚ] L, σ (b : L)/(b : L)=((ψ σ : Lˣ) : L) := by
  let f : (L ≃ₐ[ℚ] L) → Lˣ := fun σ => (ψ σ : Lˣ)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro σ τ
    apply Units.ext
    change ((ψ (σ*τ) : Lˣ) : L)=σ ((ψ τ : Lˣ) : L)*((ψ σ : Lˣ) : L)
    rw [ψ.map_mul]
    change ((ψ σ : Lˣ) : L)*((ψ τ : Lˣ) : L)=σ ((ψ τ : Lˣ) : L)*((ψ σ : Lˣ) : L)
    rw [actual_square_one_aut_fixed]
    exact mul_comm _ _
  obtain ⟨b,hb⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨b,?_⟩
  intro σ
  have h := congrArg (fun u : Lˣ => (u : L)) (hb σ)
  simpa only [AlgEquiv.smul_units_def,Units.val_div_eq_div_val,Units.coe_map,MonoidHom.coe_ofClass] using h

end ActualTwoDescentFiniteCharacterHilbert318
