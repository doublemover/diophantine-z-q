module
public import ActualTwoDescentGlobalCharacterEigenvector318
public section
noncomputable section
namespace ActualTwoDescentGlobalCharacterSquareRoot318
set_option maxHeartbeats 16000000

open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentScalarConnectingHom318 ActualTwoDescentGlobalCharacterEigenvector318
open ActualTwoDescentGaloisFixedRational318

/-- The eigenvector square descends to an actual nonzero RATIONAL scalar. -/
theorem actual_global_character_square_root (χ : continuousCharacters) :
    ∃ a : ℚˣ, ∃ r : Qbar, r ≠ 0 ∧ r^2=algebraMap ℚ Qbar (a : ℚ) ∧
      ∀ σ : GalQ, σ r/r=(((χ : GalQ →* SquareOne Qbar) σ : Qbarˣ) : Qbar) := by
  obtain ⟨r,hr,hχ⟩ := actual_global_character_eigenvector χ
  have hfix (σ : GalQ) : σ (r^2)=r^2 := by
    have he := (div_eq_iff hr).mp (hχ σ)
    rw [map_pow,he,mul_pow,square_one_value,one_mul]
  obtain ⟨a,ha⟩ := actual_fixed_coordinate_rational (r^2) hfix
  have han : a ≠ 0 := by
    intro he
    rw [he,map_zero] at ha
    exact pow_ne_zero 2 hr ha.symm
  exact ⟨Units.mk0 a han,r,hr,ha.symm,hχ⟩

end ActualTwoDescentGlobalCharacterSquareRoot318
