module
public import ActualCasselsTateShaLocalPrimitives318
import all ActualTwoDescentContinuousCocycleRestriction318
import all ActualTwoDescentFieldHalvingCocycle318
public section
noncomputable section
namespace ActualCasselsTateRestrictedHalf318

variable {F L : Type} [Field F] [CharZero F] [DecidableEq F]
  [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisLocallyConstant318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticHOneKernel318 ActualTwoDescentTorsionIntoFullCocycles318
open ActualTwoDescentGeometricPointTransport318 ActualTwoDescentGeometricRestrictionAction318
open ActualTwoDescentContinuousCocycleRestriction318 ActualTwoDescentSquareClassFieldMap318
open ActualCasselsTateFirstCochainLift318 ActualCasselsTateLocalAdjustment318

/-- Literal base change of the chosen GLOBAL half-cochain; no commuting-choice
assertion with the independently chosen local half-cochain. -/
def restrictedHalf (f : F →+* L) (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (σ : Field.absoluteGaloisGroup L) : Point (algebraMap L (AlgebraicClosure L) (f n)) :=
  closurePointMap f n hn (halfCochain n hn χ (Field.absoluteGaloisGroup.map f σ))

lemma restrictedHalf_double (f : F →+* L) (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (σ : Field.absoluteGaloisGroup L) :
    2 • restrictedHalf f n hn χ σ=originalValue (f n) (cocycleRestriction f n hn χ) σ := by
  rw [restrictedHalf,←map_nsmul,halfCochain_double]
  exact actual_closure_point_torsion f n hn
    ((χ : Field.absoluteGaloisGroup F →* Multiplicative (closedTwoTorsion n))
      (Field.absoluteGaloisGroup.map f σ))

lemma restrictedHalf_locally_constant (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ : continuousCocycles n) : IsLocallyConstant (restrictedHalf f n hn χ) :=
  ((halfCochain_locally_constant n hn χ).comp_continuous
    (Field.absoluteGaloisGroup.map f).continuous).comp (closurePointMap f n hn)

lemma restrictedHalf_coboundary (f : F →+* L) (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (σ τ : Field.absoluteGaloisGroup L) :
    galoisPointHom σ (f n) (field_map_ne_zero f hn) (restrictedHalf f n hn χ τ)-
      restrictedHalf f n hn χ (σ*τ)+restrictedHalf f n hn χ σ=
      closurePointMap f n hn (halfDefect n hn χ
        (Field.absoluteGaloisGroup.map f σ) (Field.absoluteGaloisGroup.map f τ)) := by
  simp only [restrictedHalf,halfDefect,map_sub,map_add,map_mul,actual_closure_point_galois]

/-- Correction of the restricted global half by a local actual geometric
coboundary. Its defect is the transferred GLOBAL defect, not a freshly chosen one. -/
def restrictedAdjustment (f : F →+* L) (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (Q : Point (algebraMap L (AlgebraicClosure L) (f n)))
    (σ : Field.absoluteGaloisGroup L) : Point (algebraMap L (AlgebraicClosure L) (f n)) :=
  restrictedHalf f n hn χ σ-
    halfDifference (f n) (field_map_ne_zero f hn) (actualHalf (f n) (field_map_ne_zero f hn) Q) σ

lemma restrictedAdjustment_two (f : F →+* L) (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (Q : Point (algebraMap L (AlgebraicClosure L) (f n)))
    (hQ : ∀ σ : Field.absoluteGaloisGroup L,
      originalValue (f n) (cocycleRestriction f n hn χ) σ=
        halfDifference (f n) (field_map_ne_zero f hn) Q σ)
    (σ : Field.absoluteGaloisGroup L) : 2 • restrictedAdjustment f n hn χ Q σ=0 := by
  rw [restrictedAdjustment,nsmul_sub,restrictedHalf_double,boundary_half_double,hQ,sub_self]

lemma restrictedAdjustment_locally_constant (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ : continuousCocycles n) (Q : Point (algebraMap L (AlgebraicClosure L) (f n))) :
    IsLocallyConstant (restrictedAdjustment f n hn χ Q) :=
  ((restrictedHalf_locally_constant f n hn χ).prodMk
    (actual_galois_point_locally_constant (f n) (field_map_ne_zero f hn)
      (actualHalf (f n) (field_map_ne_zero f hn) Q))).comp
      (fun z => z.1-(z.2-actualHalf (f n) (field_map_ne_zero f hn) Q))

lemma restrictedAdjustment_coboundary (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ : continuousCocycles n) (Q : Point (algebraMap L (AlgebraicClosure L) (f n)))
    (σ τ : Field.absoluteGaloisGroup L) :
    galoisPointHom σ (f n) (field_map_ne_zero f hn) (restrictedAdjustment f n hn χ Q τ)-
      restrictedAdjustment f n hn χ Q (σ*τ)+restrictedAdjustment f n hn χ Q σ=
      closurePointMap f n hn (halfDefect n hn χ
        (Field.absoluteGaloisGroup.map f σ) (Field.absoluteGaloisGroup.map f τ)) := by
  rw [←restrictedHalf_coboundary]
  simp only [restrictedAdjustment,map_sub,actual_half_difference_cocycle]
  abel

/-- The local full-class zero condition produces a continuous E[2] correction
whose coboundary is the literal transported global defect. -/
theorem restricted_global_correction (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ : continuousCocycles n)
    (hz : fullClassHom (f n) (field_map_ne_zero f hn)
      (torsionFullCocycle (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ))=0) :
    ∃ b : Field.absoluteGaloisGroup L → closedTwoTorsion (f n), IsLocallyConstant b ∧
      ∀ σ τ : Field.absoluteGaloisGroup L,
        (b τ : Point (algebraMap L (AlgebraicClosure L) (f n)))-
          (b (σ*τ) : Point (algebraMap L (AlgebraicClosure L) (f n)))+
          (b σ : Point (algebraMap L (AlgebraicClosure L) (f n)))=
        closurePointMap f n hn (halfDefect n hn χ
          (Field.absoluteGaloisGroup.map f σ) (Field.absoluteGaloisGroup.map f τ)) := by
  obtain ⟨Q,hQ⟩ := (actual_full_class_zero (f n) (field_map_ne_zero f hn)
    (torsionFullCocycle (f n) (field_map_ne_zero f hn) (cocycleRestriction f n hn χ))).mp hz
  have hQ' : ∀ σ : Field.absoluteGaloisGroup L,
      originalValue (f n) (cocycleRestriction f n hn χ) σ=
        halfDifference (f n) (field_map_ne_zero f hn) Q σ := hQ
  let b : Field.absoluteGaloisGroup L → closedTwoTorsion (f n) := fun σ =>
    ⟨restrictedAdjustment f n hn χ Q σ,restrictedAdjustment_two f n hn χ Q hQ' σ⟩
  refine ⟨b,?_,?_⟩
  · apply IsLocallyConstant.desc b
      (fun T : closedTwoTorsion (f n) => (T : Point (algebraMap L (AlgebraicClosure L) (f n))))
    · exact restrictedAdjustment_locally_constant f n hn χ Q
    · intro x y h
      exact Subtype.ext h
  · intro σ τ
    have h := restrictedAdjustment_coboundary f n hn χ Q σ τ
    have hf : galoisPointHom σ (f n) (field_map_ne_zero f hn)
        (restrictedAdjustment f n hn χ Q τ)=restrictedAdjustment f n hn χ Q τ :=
      actual_two_torsion_fixed_subtype σ (f n) (field_map_ne_zero f hn) (b τ)
    rw [hf] at h
    exact h

end ActualCasselsTateRestrictedHalf318
