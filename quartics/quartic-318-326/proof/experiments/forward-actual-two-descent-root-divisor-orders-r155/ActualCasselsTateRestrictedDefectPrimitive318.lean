module
public import ActualCasselsTateRestrictedHalf318
public import ActualTwoDescentCupRestriction318
import all ActualTwoDescentOriginalTorsionPairing318
import all ActualTwoDescentContinuousCocycleRestriction318
public section
noncomputable section
namespace ActualCasselsTateRestrictedDefectPrimitive318

variable {F L : Type} [Field F] [CharZero F] [DecidableEq F]
  [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentTorsionIntoFullCocycles318 ActualTwoDescentGeometricRestrictionAction318
open ActualTwoDescentGeometricPointTransport318 ActualTwoDescentSquareClassFieldMap318
open ActualTwoDescentContinuousCocycleRestriction318 ActualTwoDescentTorsionCoefficientTransfer318
open ActualTwoDescentOriginalTorsionPairing318 ActualTwoDescentCupRestriction318
open ActualCasselsTateFirstCochainLift318 ActualCasselsTateDefectCup318
open ActualCasselsTateLocalCupCorrection318 ActualCasselsTateRestrictedHalf318

lemma original_pairing_transfer (f : F →+* L) (n : F) (hn : n ≠ 0)
    (P Q : closedTwoTorsion n) :
    originalTorsionPairing (f n) (field_map_ne_zero f hn)
      (torsionCoefficientTransfer f n hn (Multiplicative.ofAdd P)).toAdd
      (torsionCoefficientTransfer f n hn (Multiplicative.ofAdd Q)).toAdd=
      originalTorsionPairing n hn P Q := by
  unfold originalTorsionPairing
  rw [actual_original_torsion_binary_transfer,actual_original_torsion_binary_transfer]

/-- Local triviality of the actual class bounds the literal restriction of
the GLOBAL coordinate defect cup. No equality of chosen halves is assumed. -/
theorem restricted_global_cup_primitive (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n)
    (hz : fullClassHom (f n) (field_map_ne_zero f hn)
      (torsionFullCocycle (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ))=0) :
    ∃ c : Field.absoluteGaloisGroup L → Field.absoluteGaloisGroup L → ZMod 2,
      IsLocallyConstant (fun g : Field.absoluteGaloisGroup L × Field.absoluteGaloisGroup L => c g.1 g.2) ∧
      ∀ σ τ υ : Field.absoluteGaloisGroup L,
        c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
          defectCup n hn χ ψ (Field.absoluteGaloisGroup.map f σ)
            (Field.absoluteGaloisGroup.map f τ) (Field.absoluteGaloisGroup.map f υ) := by
  obtain ⟨b,hb,hd⟩ := restricted_global_correction f n hn χ hz
  refine ⟨correctionCup (f n) (field_map_ne_zero f hn) b (cocycleRestriction f n hn ψ),
    correctionCup_locally_constant _ _ b hb _,?_⟩
  intro σ τ υ
  let D : closedTwoTorsion (f n) :=
    (torsionCoefficientTransfer f n hn (Multiplicative.ofAdd
      (torsionDefect n hn χ (Field.absoluteGaloisGroup.map f σ)
        (Field.absoluteGaloisGroup.map f τ)))).toAdd
  have hD : (D : Point (algebraMap L (AlgebraicClosure L) (f n)))=
      closurePointMap f n hn (halfDefect n hn χ
        (Field.absoluteGaloisGroup.map f σ) (Field.absoluteGaloisGroup.map f τ)) :=
    (actual_closure_point_torsion f n hn (Multiplicative.ofAdd
      (torsionDefect n hn χ (Field.absoluteGaloisGroup.map f σ)
        (Field.absoluteGaloisGroup.map f τ)))).symm
  have hs : b τ+b σ=D+b (σ*τ) := by
    apply Subtype.ext
    change (b τ : Point (algebraMap L (AlgebraicClosure L) (f n)))+
      (b σ : Point (algebraMap L (AlgebraicClosure L) (f n)))=
      (D : Point (algebraMap L (AlgebraicClosure L) (f n)))+
        (b (σ*τ) : Point (algebraMap L (AlgebraicClosure L) (f n)))
    rw [hD,←hd σ τ]
    abel
  have h := congrArg (fun T => originalTorsionPairing (f n) (field_map_ne_zero f hn) T
    (torsionValue (f n) (cocycleRestriction f n hn ψ) υ)) hs
  simp only [actual_original_pairing_add_left] at h
  calc
    _ = originalTorsionPairing (f n) (field_map_ne_zero f hn) D
        (torsionValue (f n) (cocycleRestriction f n hn ψ) υ) := by
      simp only [correctionCup,torsionValue_mul,actual_original_pairing_add_right]
      calc
        _ = (originalTorsionPairing (f n) (field_map_ne_zero f hn) (b τ)
          (torsionValue (f n) (cocycleRestriction f n hn ψ) υ)+
          originalTorsionPairing (f n) (field_map_ne_zero f hn) (b σ)
          (torsionValue (f n) (cocycleRestriction f n hn ψ) υ))-
          originalTorsionPairing (f n) (field_map_ne_zero f hn) (b (σ*τ))
          (torsionValue (f n) (cocycleRestriction f n hn ψ) υ) := by abel
        _ = _ := by rw [h]; abel
    _ = _ := original_pairing_transfer f n hn
      (torsionDefect n hn χ (Field.absoluteGaloisGroup.map f σ)
        (Field.absoluteGaloisGroup.map f τ))
      (torsionValue n ψ (Field.absoluteGaloisGroup.map f υ))

end ActualCasselsTateRestrictedDefectPrimitive318
