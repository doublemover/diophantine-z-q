module
public import ActualTwoDescentContinuousEllipticCocycles318
public section
noncomputable section
namespace ActualTwoDescentFullEllipticHOneKernel318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisLocallyConstant318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldActualCohomologicalImage318
open groupCohomology

open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentContinuousEllipticCocycles318

/-- Exact coboundary criterion inside Mathlib H1 of the ACTUAL full geometric representation. -/
lemma actual_full_class_zero (n : F) (hn : n ≠ 0) (z : continuousFullCocycles n hn) :
    fullClassHom n hn z=0 ↔ ∃ Q : Point (algebraMap F Qbar n),
      ∀ σ : Gal, (z.val : Gal → Point (algebraMap F Qbar n)) σ=halfDifference n hn Q σ := by
  change H1π _ z.val=0 ↔ _
  rw [H1π_eq_zero_iff]
  constructor
  · rintro ⟨Q,hQ⟩
    exact ⟨Q,fun σ => (congrFun hQ σ).symm⟩
  · rintro ⟨Q,hQ⟩
    exact ⟨Q,funext (fun σ => (hQ σ).symm)⟩

/-- Only classes admitting genuinely locally constant cocycles are called continuous here. -/
def continuousFullHOne (n : F) (hn : n ≠ 0) : AddSubgroup (H1 (fullEllipticRep n hn)) :=
  (fullClassHom n hn).range

end ActualTwoDescentFullEllipticHOneKernel318
