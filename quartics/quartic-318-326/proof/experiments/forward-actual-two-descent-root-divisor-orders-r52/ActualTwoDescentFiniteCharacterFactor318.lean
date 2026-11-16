module
public import ActualTwoDescentSurjectiveCharacterFactor318
public section
noncomputable section
namespace ActualTwoDescentFiniteCharacterFactor318
set_option maxHeartbeats 16000000

open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentScalarConnectingHom318 ActualTwoDescentSurjectiveCharacterFactor318
open scoped Topology

/-- Local constancy produces a genuine finite NORMAL subextension through which the character factors. -/
theorem actual_finite_character_factor (χ : continuousCharacters) :
    ∃ L : IntermediateField ℚ Qbar, ∃ hf : FiniteDimensional ℚ L, ∃ hN : Normal ℚ L,
      letI := hN
      ∃ ψ : (L ≃ₐ[ℚ] L) →* SquareOne Qbar,
        ∀ σ : GalQ, ψ (σ.restrictNormal L)=(χ : GalQ →* SquareOne Qbar) σ := by
  have ho : IsOpen {σ : GalQ | (χ : GalQ →* SquareOne Qbar) σ=1} := χ.property.isOpen_fiber 1
  have hn : {σ : GalQ | (χ : GalQ →* SquareOne Qbar) σ=1} ∈ 𝓝 (1 : GalQ) :=
    ho.mem_nhds (χ : GalQ →* SquareOne Qbar).map_one
  obtain ⟨L,hf,hN,hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal ℚ Qbar _).mp hn
  letI := hN
  let f : GalQ →* (L ≃ₐ[ℚ] L) := AlgEquiv.restrictNormalHom L
  have hsur : Function.Surjective f := AlgEquiv.restrictNormalHom_surjective Qbar
  have hk : f.ker ≤ (χ : GalQ →* SquareOne Qbar).ker := by
    intro σ hσ
    apply hL
    change σ ∈ (AlgEquiv.restrictNormalHom L : GalQ →* (L ≃ₐ[ℚ] L)).ker at hσ
    rw [L.restrictNormalHom_ker] at hσ
    exact hσ
  refine ⟨L,hf,hN,surjectiveCharacterFactor f hsur χ hk,?_⟩
  intro σ
  exact actual_surjective_factor_value f hsur χ hk σ

end ActualTwoDescentFiniteCharacterFactor318
