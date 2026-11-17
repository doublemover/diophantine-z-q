module
public import ActualCasselsTateRestrictedDefectPrimitive318
public section
noncomputable section
namespace ActualCasselsTateEverywherePrimitive318

variable {F L : Type} [Field F] [CharZero F] [DecidableEq F]
  [Field L] [CharZero L] [DecidableEq L]
open ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentContinuousEllipticCocycles318 ActualTwoDescentTorsionIntoFullCocycles318
open ActualTwoDescentActualShaDefinition318 ActualTwoDescentFullCocycleRestriction318
open ActualCasselsTateDefectCup318 ActualCasselsTateShaLocalPrimitives318
open ActualCasselsTateRestrictedDefectPrimitive318
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- A continuous primitive of the literal field restriction of the global
coordinate defect. This asserts no Brauer interpretation or local value. -/
def HasRestrictedCoordinatePrimitive (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n) : Prop :=
  ∃ c : Field.absoluteGaloisGroup L → Field.absoluteGaloisGroup L → ZMod 2,
    IsLocallyConstant (fun g : Field.absoluteGaloisGroup L × Field.absoluteGaloisGroup L => c g.1 g.2) ∧
    ∀ σ τ υ : Field.absoluteGaloisGroup L,
      c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
        defectCup n hn χ ψ (Field.absoluteGaloisGroup.map f σ)
          (Field.absoluteGaloisGroup.map f τ) (Field.absoluteGaloisGroup.map f υ)

/-- The actual Sha representative condition produces the real and ALL finite
place primitives of the SAME global coordinate defect. Global degree-three
vanishing, geometric Weil identification and invariant summation remain open. -/
theorem actual_sha_everywhere_primitive (n : ℚ) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n)
    (hSha : fullClassHom n hn (torsionFullCocycle n hn χ) ∈ actualSha n hn) :
    HasRestrictedCoordinatePrimitive (algebraMap ℚ ℝ) n hn χ ψ ∧
      ∀ (p : ℕ) [Fact p.Prime],
        HasRestrictedCoordinatePrimitive (algebraMap ℚ (ℚ_[p])) n hn χ ψ := by
  have hz := torsion_representative_everywhere n hn χ hSha
  constructor
  · apply restricted_global_cup_primitive
    have h := hz.1
    rw [actual_full_restriction_torsion] at h
    exact h
  · intro p hp
    apply restricted_global_cup_primitive
    have h := hz.2 p
    rw [actual_full_restriction_torsion] at h
    exact h

end ActualCasselsTateEverywherePrimitive318
