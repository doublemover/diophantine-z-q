module
public import ActualTwoDescentGaloisImageCardinality318
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public section
noncomputable section
namespace ActualTwoDescentActualGaloisCohomology318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentGaloisPointAction318 ActualTwoDescentGaloisTwoTorsion318
open ActualTwoDescentHalvingChoiceIndependence318 ActualTwoDescentGaloisConnectingHom318
open ActualTwoDescentGaloisLocallyConstant318
open groupCohomology
local instance : DecidableEq Qbar := Classical.decEq _

abbrev actualTwoTorsionRep (n : ℚ) : Rep ℤ GalQ := Rep.trivial ℤ GalQ (closedTwoTorsion n)

/-- The chosen representation is identified with the ACTUAL Galois action on E[2]. -/
lemma actual_rep_action_agrees (n : ℚ) (hn : n ≠ 0) (σ : GalQ) (T : closedTwoTorsion n) :
    ((actualTwoTorsionRep n).ρ σ T : Point (algebraMap ℚ Qbar n))=galoisPointHom σ n hn T := by
  rw [Representation.isTrivial_apply]
  exact (actual_two_torsion_fixed_subtype σ n hn T).symm

def actualGaloisCocycle (n : ℚ) (hn : n ≠ 0) (P : Point n) : cocycles₁ (actualTwoTorsionRep n) :=
  ⟨fun σ => (rationalHalvingCocycle n hn P σ).toAdd,by
    apply (mem_cocycles₁_iff _).mpr
    intro σ τ
    rw [Representation.isTrivial_apply]
    have h := congrArg Multiplicative.toAdd ((rationalHalvingCocycle n hn P).map_mul σ τ)
    exact h.trans (add_comm _ _)⟩

lemma actual_galois_cocycle_add (n : ℚ) (hn : n ≠ 0) (P Q : Point n) :
    actualGaloisCocycle n hn (P+Q)=actualGaloisCocycle n hn P+actualGaloisCocycle n hn Q := by
  apply Subtype.ext
  funext σ
  change (rationalHalvingCocycle n hn (P+Q) σ).toAdd=
    (rationalHalvingCocycle n hn P σ).toAdd+(rationalHalvingCocycle n hn Q σ).toAdd
  rw [actual_halving_cocycle_add]
  rfl

lemma actual_galois_cocycle_locally_constant (n : ℚ) (hn : n ≠ 0) (P : Point n) :
    IsLocallyConstant (actualGaloisCocycle n hn P) :=
  (actual_halving_cocycle_locally_constant n hn P).comp Multiplicative.toAdd

end ActualTwoDescentActualGaloisCohomology318
