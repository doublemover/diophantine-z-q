module
public import ActualCasselsTateLocalCupCorrection318
public import ActualTwoDescentActualShaDefinition318
import all ActualTwoDescentActualShaDefinition318
public section
noncomputable section
namespace ActualCasselsTateShaLocalPrimitives318

variable {F L : Type} [Field F] [CharZero F] [DecidableEq F]
  [Field L] [CharZero L] [DecidableEq L]
open ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentContinuousEllipticCocycles318 ActualTwoDescentTorsionIntoFullCocycles318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentFullLocalClassRestriction318
open ActualTwoDescentContinuousCocycleRestriction318 ActualTwoDescentSquareClassFieldMap318
open ActualTwoDescentActualShaDefinition318 ActualCasselsTateDefectCup318
open ActualCasselsTateLocalCupCorrection318
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Equality of actual full classes transports local triviality to the
specified torsion representative, using the existing literal restriction square. -/
lemma restricted_torsion_class_zero (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ : continuousCocycles n) (z : continuousFullCocycles n hn)
    (he : fullClassHom n hn (torsionFullCocycle n hn χ)=fullClassHom n hn z)
    (hz : fullClassHom (f n) (field_map_ne_zero f hn) (fullCocycleRestriction f n hn z)=0) :
    fullClassHom (f n) (field_map_ne_zero f hn)
      (torsionFullCocycle (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ))=0 := by
  have h := actual_full_local_class_eq f n hn (torsionFullCocycle n hn χ) z he
  rw [actual_full_restriction_torsion] at h
  exact h.trans hz

/-- The given torsion representative of an actual Sha class itself has zero
full local class at every place; no change of Sha or coordinate quotient. -/
lemma torsion_representative_everywhere (n : ℚ) (hn : n ≠ 0) (χ : continuousCocycles n)
    (hSha : fullClassHom n hn (torsionFullCocycle n hn χ) ∈ actualSha n hn) :
    EverywhereLocallyTrivial n hn (torsionFullCocycle n hn χ) := by
  obtain ⟨z,hz,hR,hp⟩ := hSha
  constructor
  · exact (actual_full_local_class_eq (algebraMap ℚ ℝ) n hn
      (torsionFullCocycle n hn χ) z hz.symm).trans hR
  · intro p hp'
    exact (actual_full_local_class_eq (algebraMap ℚ (ℚ_[p])) n hn
      (torsionFullCocycle n hn χ) z hz.symm).trans (hp p)

/-- A local coordinate primitive for the exact restricted representatives.
The cochain has not been identified with a geometric Weil/Brauer cochain. -/
theorem restricted_local_cup_primitive (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n)
    (hz : fullClassHom (f n) (field_map_ne_zero f hn)
      (fullCocycleRestriction f n hn (torsionFullCocycle n hn χ))=0) :
    ∃ c : Field.absoluteGaloisGroup L → Field.absoluteGaloisGroup L → ZMod 2,
      IsLocallyConstant (fun g : Field.absoluteGaloisGroup L × Field.absoluteGaloisGroup L => c g.1 g.2) ∧
      ∀ σ τ υ : Field.absoluteGaloisGroup L,
        c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
          defectCup (f n) (field_map_ne_zero f hn)
            (cocycleRestriction f n hn χ) (cocycleRestriction f n hn ψ) σ τ υ := by
  rw [actual_full_restriction_torsion] at hz
  exact local_cup_primitive (f n) (field_map_ne_zero f hn)
    (cocycleRestriction f n hn χ) (cocycleRestriction f n hn ψ) hz

/-- Every finite-place local primitive follows from membership in the actual
Sha subgroup, not from a new local solvability premise. -/
theorem actual_sha_padic_primitive (n : ℚ) (hn : n ≠ 0) (χ ψ : continuousCocycles n)
    (hSha : fullClassHom n hn (torsionFullCocycle n hn χ) ∈ actualSha n hn)
    (p : ℕ) [Fact p.Prime] :
    ∃ c : Field.absoluteGaloisGroup (ℚ_[p]) → Field.absoluteGaloisGroup (ℚ_[p]) → ZMod 2,
      IsLocallyConstant (fun g : Field.absoluteGaloisGroup (ℚ_[p]) × Field.absoluteGaloisGroup (ℚ_[p]) => c g.1 g.2) ∧
      ∀ σ τ υ : Field.absoluteGaloisGroup (ℚ_[p]),
        c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
          defectCup ((algebraMap ℚ (ℚ_[p])) n) (field_map_ne_zero _ hn)
            (cocycleRestriction (algebraMap ℚ (ℚ_[p])) n hn χ)
            (cocycleRestriction (algebraMap ℚ (ℚ_[p])) n hn ψ) σ τ υ := by
  exact restricted_local_cup_primitive (algebraMap ℚ (ℚ_[p])) n hn χ ψ
    ((torsion_representative_everywhere n hn χ hSha).2 p)

/-- The archimedean primitive for the same actual representative. -/
theorem actual_sha_real_primitive (n : ℚ) (hn : n ≠ 0) (χ ψ : continuousCocycles n)
    (hSha : fullClassHom n hn (torsionFullCocycle n hn χ) ∈ actualSha n hn) :
    ∃ c : Field.absoluteGaloisGroup ℝ → Field.absoluteGaloisGroup ℝ → ZMod 2,
      IsLocallyConstant (fun g : Field.absoluteGaloisGroup ℝ × Field.absoluteGaloisGroup ℝ => c g.1 g.2) ∧
      ∀ σ τ υ : Field.absoluteGaloisGroup ℝ,
        c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
          defectCup ((algebraMap ℚ ℝ) n) (field_map_ne_zero _ hn)
            (cocycleRestriction (algebraMap ℚ ℝ) n hn χ)
            (cocycleRestriction (algebraMap ℚ ℝ) n hn ψ) σ τ υ := by
  exact restricted_local_cup_primitive (algebraMap ℚ ℝ) n hn χ ψ
    (torsion_representative_everywhere n hn χ hSha).1

end ActualCasselsTateShaLocalPrimitives318
