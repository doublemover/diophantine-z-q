module
public import ActualTwoDescentGeometricPowerTorsion318
public section
noncomputable section
namespace ActualTwoDescentFullBoundaryHom318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology

def fullBoundaryHom (n : F) (hn : n ≠ 0) :
    Point (algebraMap F Qbar n) →+ continuousFullCocycles n hn where
  toFun := fullBoundary n hn
  map_zero' := by apply Subtype.ext; apply Subtype.ext; funext σ; simp [fullBoundary,halfDifference]
  map_add' := actual_full_boundary_add n hn

lemma actual_boundary_nsmul (n : F) (hn : n ≠ 0) (Q) (m : ℕ) :
    fullBoundary n hn (m • Q)=m • fullBoundary n hn Q := map_nsmul (fullBoundaryHom n hn) Q m

lemma actual_difference_nsmul (n : F) (hn : n ≠ 0) (Q) (m : ℕ) (σ : Gal) :
    halfDifference n hn (m • Q) σ=m • halfDifference n hn Q σ := by
  simp only [halfDifference,map_nsmul,nsmul_sub]

lemma actual_rational_boundary_zero (n : F) (hn : n ≠ 0) (P : Point n) :
    fullBoundary n hn (rationalPointMap n hn P)=0 := by
  apply Subtype.ext; apply Subtype.ext; funext σ
  change halfDifference n hn (rationalPointMap n hn P) σ=0
  rw [halfDifference,actual_rational_point_fixed,sub_self]

end ActualTwoDescentFullBoundaryHom318
