module
public import ActualCasselsTateRestrictedHalf318
import all ActualCasselsTateFirstCochainLift318
import all ActualCasselsTateLocalAdjustment318
import all ActualTwoDescentFieldGaloisFixedRational318
public section
noncomputable section
namespace ActualCasselsTateKummerFourLocalLift318
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentFieldContinuousGaloisCocycles318
open ActualCasselsTateFirstCochainLift318 ActualCasselsTateLocalAdjustment318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "G" => Field.absoluteGaloisGroup F
local notation "K" => AlgebraicClosure F
local instance : DecidableEq K := Classical.decEq _

/-- The actual choice of Q witnessing full local triviality gives a
Kummer lift, not just a possible primitive of the coordinate defect.
R is base-rational, 4S=R, and the local crossed homomorphism δS projects
pointwise to the very same representative χ. -/
theorem local_kummer_four (n : F) (hn : n ≠ 0) (χ : continuousCocycles n)
    (Q : Point (algebraMap F K n))
    (hQ : ∀ σ : G, originalValue n χ σ = halfDifference n hn Q σ) :
    ∃ R : Point n, rationalPointMap n hn R = 2 • Q ∧
      4 • actualHalf n hn Q = rationalPointMap n hn R ∧
      ∀ σ : G, 2 • halfDifference n hn (actualHalf n hn Q) σ = originalValue n χ σ ∧
        4 • halfDifference n hn (actualHalf n hn Q) σ = 0 := by
  have hfix (σ : G) : galoisPointHom σ n hn (2 • Q)=2 • Q := by
    apply sub_eq_zero.mp
    rw [map_nsmul,←nsmul_sub]
    exact (congrArg (fun P : Point (algebraMap F K n) => 2 • P) (hQ σ)).symm.trans
      (originalValue_two n χ σ)
  obtain ⟨R,hR⟩ := actual_fixed_point_rational n hn (2 • Q) hfix
  have hs : 2 • actualHalf n hn Q = Q := by
    rw [two_nsmul]
    exact actual_half_spec n hn Q
  refine ⟨R,hR,?_,?_⟩
  · calc
      4 • actualHalf n hn Q = 2 • (2 • actualHalf n hn Q) := by rw [←mul_smul]
      _ = _ := by rw [hs,hR]
  · intro σ
    have h := (boundary_half_double n hn Q σ).trans (hQ σ).symm
    refine ⟨h,?_⟩
    calc
      4 • halfDifference n hn (actualHalf n hn Q) σ =
          2 • (2 • halfDifference n hn (actualHalf n hn Q) σ) := by rw [←mul_smul]
      _ = 0 := by rw [h,originalValue_two]
end ActualCasselsTateKummerFourLocalLift318
