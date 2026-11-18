module
public import ActualCasselsTateLocalAdjustment318
public section
noncomputable section
namespace ActualCasselsTateLocalCupCorrection318

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentTorsionIntoFullCocycles318 ActualTwoDescentOriginalTorsionPairing318
open ActualCasselsTateFirstCochainLift318 ActualCasselsTateDefectCup318
open ActualCasselsTateLocalAdjustment318

/-- The local degree-two cup correction, with the original coordinate form.
This is not yet a Brauer cocycle or a local invariant. -/
def correctionCup (n : F) (hn : n ≠ 0) (b : Gal → closedTwoTorsion n)
    (ψ : continuousCocycles n) (σ τ : Gal) : ZMod 2 :=
  originalTorsionPairing n hn (b σ) (torsionValue n ψ τ)

lemma correctionCup_locally_constant (n : F) (hn : n ≠ 0)
    (b : Gal → closedTwoTorsion n) (hb : IsLocallyConstant b) (ψ : continuousCocycles n) :
    IsLocallyConstant (fun g : Gal × Gal => correctionCup n hn b ψ g.1 g.2) := by
  have hp : IsLocallyConstant (torsionValue n ψ) :=
    ψ.property.comp (fun T : Multiplicative (closedTwoTorsion n) => T.toAdd)
  exact ((hb.comp_continuous continuous_fst).prodMk
    (hp.comp_continuous continuous_snd)).comp
    (fun z => originalTorsionPairing n hn z.1 z.2)

lemma correctionCup_coboundary (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n)
    (b : Gal → closedTwoTorsion n)
    (hb : ∀ σ τ : Gal, (b τ : Point (algebraMap F Qbar n))-
      (b (σ*τ) : Point (algebraMap F Qbar n))+(b σ : Point (algebraMap F Qbar n))=
        halfDefect n hn χ σ τ) (σ τ υ : Gal) :
    correctionCup n hn b ψ τ υ-correctionCup n hn b ψ (σ*τ) υ+
      correctionCup n hn b ψ σ (τ*υ)-correctionCup n hn b ψ σ τ=
        defectCup n hn χ ψ σ τ υ := by
  have hs : b τ+b σ=torsionDefect n hn χ σ τ+b (σ*τ) := by
    apply Subtype.ext
    change (b τ : Point (algebraMap F Qbar n))+(b σ : Point (algebraMap F Qbar n))=
      halfDefect n hn χ σ τ+(b (σ*τ) : Point (algebraMap F Qbar n))
    rw [←hb σ τ]
    abel
  have h := congrArg (fun T => originalTorsionPairing n hn T (torsionValue n ψ υ)) hs
  simp only [actual_original_pairing_add_left] at h
  simp only [correctionCup,torsionValue_mul,actual_original_pairing_add_right,defectCup]
  calc
    _ = (originalTorsionPairing n hn (b τ) (torsionValue n ψ υ)+
      originalTorsionPairing n hn (b σ) (torsionValue n ψ υ))-
      originalTorsionPairing n hn (b (σ*τ)) (torsionValue n ψ υ) := by abel
    _ = _ := by rw [h]; abel

/-- Actual full-class vanishing produces a continuous local primitive of the
coordinate degree-three defect. No global vanishing is assumed or concluded. -/
theorem local_cup_primitive (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n)
    (hz : fullClassHom n hn (torsionFullCocycle n hn χ)=0) :
    ∃ c : Gal → Gal → ZMod 2,
      IsLocallyConstant (fun g : Gal × Gal => c g.1 g.2) ∧
      ∀ σ τ υ : Gal, c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
        defectCup n hn χ ψ σ τ υ := by
  obtain ⟨b,hb,hd⟩ := local_correction_of_full_class_zero n hn χ hz
  exact ⟨correctionCup n hn b ψ,correctionCup_locally_constant n hn b hb ψ,
    correctionCup_coboundary n hn χ ψ b hd⟩

end ActualCasselsTateLocalCupCorrection318
