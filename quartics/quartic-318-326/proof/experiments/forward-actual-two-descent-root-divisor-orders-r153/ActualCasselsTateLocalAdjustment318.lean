module
public import ActualCasselsTateDefectCup318
public import ActualTwoDescentTorsionIntoFullCocycles318
import all ActualTwoDescentTorsionIntoFullCocycles318
import all ActualTwoDescentFieldHalvingCocycle318
public section
noncomputable section
namespace ActualCasselsTateLocalAdjustment318

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldGaloisLocallyConstant318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticHOneKernel318 ActualTwoDescentTorsionIntoFullCocycles318
open ActualCasselsTateFirstCochainLift318 ActualCasselsTateContinuousDefect318

/-- The local half-cochain corrected by a genuine geometric coboundary. -/
def adjustment (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (Q : Point (algebraMap F Qbar n)) (σ : Gal) : Point (algebraMap F Qbar n) :=
  halfCochain n hn χ σ-halfDifference n hn (actualHalf n hn Q) σ

lemma boundary_half_double (n : F) (hn : n ≠ 0) (Q : Point (algebraMap F Qbar n)) (σ : Gal) :
    2 • halfDifference n hn (actualHalf n hn Q) σ=halfDifference n hn Q σ := by
  simp only [halfDifference,nsmul_sub,←map_nsmul,two_nsmul,actual_half_spec]

lemma adjustment_two (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (Q : Point (algebraMap F Qbar n))
    (hQ : ∀ σ : Gal, originalValue n χ σ=halfDifference n hn Q σ) (σ : Gal) :
    2 • adjustment n hn χ Q σ=0 := by
  rw [adjustment,nsmul_sub,halfCochain_double,boundary_half_double,hQ,sub_self]

lemma adjustment_locally_constant (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (Q : Point (algebraMap F Qbar n)) : IsLocallyConstant (adjustment n hn χ Q) :=
  ((halfCochain_locally_constant n hn χ).prodMk
    (actual_galois_point_locally_constant n hn (actualHalf n hn Q))).comp
    (fun z => z.1-(z.2-actualHalf n hn Q))

lemma adjustment_coboundary (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (Q : Point (algebraMap F Qbar n)) (σ τ : Gal) :
    galoisPointHom σ n hn (adjustment n hn χ Q τ)-adjustment n hn χ Q (σ*τ)+
      adjustment n hn χ Q σ=halfDefect n hn χ σ τ := by
  simp only [adjustment,map_sub,actual_half_difference_cocycle,halfDefect]
  abel

/-- A locally trivial ACTUAL full elliptic class supplies the needed E[2]
local correction. This is not a global trivialization or a Sha-vanishing claim. -/
theorem local_correction_of_full_class_zero (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (hz : fullClassHom n hn (torsionFullCocycle n hn χ)=0) :
    ∃ b : Gal → closedTwoTorsion n, IsLocallyConstant b ∧
      ∀ σ τ : Gal, (b τ : Point (algebraMap F Qbar n))-(b (σ*τ) : Point (algebraMap F Qbar n))+
        (b σ : Point (algebraMap F Qbar n))=halfDefect n hn χ σ τ := by
  obtain ⟨Q,hQ⟩ := (actual_full_class_zero n hn (torsionFullCocycle n hn χ)).mp hz
  have hQ' : ∀ σ : Gal, originalValue n χ σ=halfDifference n hn Q σ := hQ
  let b : Gal → closedTwoTorsion n := fun σ =>
    ⟨adjustment n hn χ Q σ,adjustment_two n hn χ Q hQ' σ⟩
  refine ⟨b,?_,?_⟩
  · apply IsLocallyConstant.desc b (fun T : closedTwoTorsion n => (T : Point (algebraMap F Qbar n)))
    · exact adjustment_locally_constant n hn χ Q
    · intro x y h
      exact Subtype.ext h
  · intro σ τ
    have h := adjustment_coboundary n hn χ Q σ τ
    have hf : galoisPointHom σ n hn (adjustment n hn χ Q τ)=adjustment n hn χ Q τ :=
      actual_two_torsion_fixed_subtype σ n hn (b τ)
    rw [hf] at h
    exact h

end ActualCasselsTateLocalAdjustment318
