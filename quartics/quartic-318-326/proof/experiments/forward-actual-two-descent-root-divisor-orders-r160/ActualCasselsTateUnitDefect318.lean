module
public import ActualCasselsTateUnitCoefficients318
public import ActualCasselsTateEverywherePrimitive318
public section
noncomputable section
namespace ActualCasselsTateUnitDefect318

open ActualCasselsTateUnitCoefficients318 ActualCasselsTateDefectCup318
open ActualCasselsTateEverywherePrimitive318
open ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualTwoDescentContinuousEllipticCocycles318 ActualTwoDescentTorsionIntoFullCocycles318
open ActualTwoDescentActualShaDefinition318
variable {F L : Type} [Field F] [CharZero F] [DecidableEq F]
  [Field L] [CharZero L] [DecidableEq L]
local notation "Gal" => Field.absoluteGaloisGroup F
local notation "Qbar" => AlgebraicClosure F
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Actual multiplicative-closure coefficients of the original coordinate
cup defect. Identification with a geometric Weil cup is still not asserted. -/
def unitDefect (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n)
    (σ τ υ : Gal) : Qbarˣ := binaryUnit (defectCup n hn χ ψ σ τ υ)

lemma unitDefect_locally_constant (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) :
    IsLocallyConstant (fun g : Gal × Gal × Gal => unitDefect n hn χ ψ g.1 g.2.1 g.2.2) :=
  (defectCup_locally_constant n hn χ ψ).comp binaryUnit

/-- The degree-three identity now holds with the genuine action on Qbarˣ. -/
lemma unitDefect_cocycle (n : F) (hn : n ≠ 0) (χ ψ : continuousCocycles n) (σ τ υ ω : Gal) :
    unitDThree (unitDefect n hn χ ψ) σ τ υ ω=1 := by
  unfold unitDefect
  rw [unitDThree_binary,defectCup_cocycle,binaryUnit_zero]

/-- Local primitives are valued in actual closure units, and bound the
literal global defect transported by the actual closure embedding. -/
def HasRestrictedUnitPrimitive (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n) : Prop :=
  ∃ c : Field.absoluteGaloisGroup L → Field.absoluteGaloisGroup L → (AlgebraicClosure L)ˣ,
    IsLocallyConstant (fun g : Field.absoluteGaloisGroup L × Field.absoluteGaloisGroup L => c g.1 g.2) ∧
    ∀ σ τ υ : Field.absoluteGaloisGroup L,
      unitDTwo c σ τ υ=closureUnitMap f
        (unitDefect n hn χ ψ (Field.absoluteGaloisGroup.map f σ)
          (Field.absoluteGaloisGroup.map f τ) (Field.absoluteGaloisGroup.map f υ))

lemma restricted_coordinate_to_unit_primitive (f : F →+* L) (n : F) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n) (h : HasRestrictedCoordinatePrimitive f n hn χ ψ) :
    HasRestrictedUnitPrimitive f n hn χ ψ := by
  obtain ⟨c,hc,hd⟩ := h
  refine ⟨fun a b => binaryUnit (c a b),hc.comp binaryUnit,?_⟩
  intro σ τ υ
  rw [unitDTwo_binary,hd]
  exact (closureUnitMap_binary f _).symm

/-- No global vanishing is assumed: actual Sha membership itself produces
unit-valued primitives at the real place and every finite place. -/
theorem actual_sha_everywhere_unit_primitive (n : ℚ) (hn : n ≠ 0)
    (χ ψ : continuousCocycles n)
    (hSha : fullClassHom n hn (torsionFullCocycle n hn χ) ∈ actualSha n hn) :
    HasRestrictedUnitPrimitive (algebraMap ℚ ℝ) n hn χ ψ ∧
      ∀ (p : ℕ) [Fact p.Prime],
        HasRestrictedUnitPrimitive (algebraMap ℚ (ℚ_[p])) n hn χ ψ := by
  have h := actual_sha_everywhere_primitive n hn χ ψ hSha
  exact ⟨restricted_coordinate_to_unit_primitive _ _ _ _ _ h.1,
    fun p hp => restricted_coordinate_to_unit_primitive _ _ _ _ _ (h.2 p)⟩

/-- Differences between two coordinate primitives of the same restricted
actual defect yield actual unit-valued degree-two cocycles. This describes
choice ambiguity; it does NOT prove the cocycle has zero local invariant. -/
lemma local_primitive_difference_cocycle
    (c d : Gal → Gal → ZMod 2)
    (h : ∀ σ τ υ : Gal,
      c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
      d τ υ-d (σ*τ) υ+d σ (τ*υ)-d σ τ) (σ τ υ : Gal) :
    unitDTwo (fun a b => binaryUnit (K:=Qbar) (c a b)/binaryUnit (d a b)) σ τ υ=1 := by
  have hd : (c τ υ-d τ υ)-(c (σ*τ) υ-d (σ*τ) υ)+
      (c σ (τ*υ)-d σ (τ*υ))-(c σ τ-d σ τ)=0 := by
    calc
      _ = (c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ)-
        (d τ υ-d (σ*τ) υ+d σ (τ*υ)-d σ τ) := by abel
      _ = 0 := by rw [h,sub_self]
  have he : (fun a b => binaryUnit (K:=Qbar) (c a b)/binaryUnit (d a b))=
      (fun a b => binaryUnit (K:=Qbar) (c a b-d a b)) := by
    funext a b
    exact (binaryUnit_sub _ _).symm
  rw [he,unitDTwo_binary,hd,binaryUnit_zero]

lemma local_primitive_difference_locally_constant
    (c d : Gal → Gal → ZMod 2)
    (hc : IsLocallyConstant (fun g : Gal × Gal => c g.1 g.2))
    (hd : IsLocallyConstant (fun g : Gal × Gal => d g.1 g.2)) :
    IsLocallyConstant (fun g : Gal × Gal =>
      binaryUnit (K:=Qbar) (c g.1 g.2)/binaryUnit (d g.1 g.2)) :=
  (hc.prodMk hd).comp (fun z => binaryUnit z.1/binaryUnit z.2)

end ActualCasselsTateUnitDefect318
