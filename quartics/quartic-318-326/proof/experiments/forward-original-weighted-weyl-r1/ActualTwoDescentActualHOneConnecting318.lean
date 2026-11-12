module
public import ActualTwoDescentActualGaloisCohomology318
public section
noncomputable section
namespace ActualTwoDescentActualHOneConnecting318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisTwoTorsion318 ActualTwoDescentHalvingChoiceIndependence318
open ActualTwoDescentGaloisConnectingKernel318 ActualTwoDescentActualGaloisCohomology318
open groupCohomology
local instance : DecidableEq Qbar := Classical.decEq _

/-- Actual H1 class of the actual, separately proved locally constant, halving cocycle. -/
def actualHOneClass (n : ℚ) (hn : n ≠ 0) (P : Point n) : H1 (actualTwoTorsionRep n) :=
  H1π (actualTwoTorsionRep n) (actualGaloisCocycle n hn P)

/-- Exact Kummer kernel in Mathlib's actual cohomology group. This does not identify a Selmer group. -/
theorem actual_hone_kernel (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    actualHOneClass n hn P=0 ↔ ∃ R : Point n, R+R=P := by
  rw [actualHOneClass,H1π_eq_zero_iff,coboundaries₁_eq_bot_of_isTrivial,Submodule.mem_bot]
  rw [←actual_galois_connecting_kernel n hn P]
  constructor
  · intro H
    apply MonoidHom.ext
    intro σ
    have h := congrFun H σ
    change (rationalHalvingCocycle n hn P σ).toAdd=0 at h
    exact congrArg Multiplicative.ofAdd h
  · intro H
    funext σ
    change (rationalHalvingCocycle n hn P σ).toAdd=0
    rw [H]
    rfl

lemma actual_hone_add (n : ℚ) (hn : n ≠ 0) (P Q : Point n) :
    actualHOneClass n hn (P+Q)=actualHOneClass n hn P+actualHOneClass n hn Q := by
  rw [actualHOneClass,actual_galois_cocycle_add,map_add]
  rfl

def actualHOneConnectingHom (n : ℚ) (hn : n ≠ 0) : Point n →+ H1 (actualTwoTorsionRep n) where
  toFun := actualHOneClass n hn
  map_zero' := (actual_hone_kernel n hn 0).mpr ⟨0,zero_add _⟩
  map_add' := actual_hone_add n hn

end ActualTwoDescentActualHOneConnecting318
