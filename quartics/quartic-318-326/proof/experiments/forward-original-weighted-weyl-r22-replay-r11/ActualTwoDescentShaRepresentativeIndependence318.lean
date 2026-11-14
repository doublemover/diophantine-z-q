module
public import ActualTwoDescentActualShaDefinition318
public section
noncomputable section
namespace ActualTwoDescentShaRepresentativeIndependence318
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

open ActualTwoDescentContinuousEllipticCocycles318 ActualTwoDescentActualShaDefinition318
open ActualTwoDescentFullLocalClassRestriction318
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

lemma actual_local_triviality_class_invariant (n : ℚ) (hn : n ≠ 0) (z w : continuousFullCocycles n hn)
    (h : fullClassHom n hn z=fullClassHom n hn w) :
    EverywhereLocallyTrivial n hn z ↔ EverywhereLocallyTrivial n hn w := by
  constructor
  · rintro ⟨hR,hp⟩
    exact ⟨(actual_full_local_class_eq (algebraMap ℚ ℝ) n hn z w h).symm.trans hR,
      fun p _ => (actual_full_local_class_eq (algebraMap ℚ (ℚ_[p])) n hn z w h).symm.trans (hp p)⟩
  · rintro ⟨hR,hp⟩
    exact ⟨(actual_full_local_class_eq (algebraMap ℚ ℝ) n hn z w h).trans hR,
      fun p _ => (actual_full_local_class_eq (algebraMap ℚ (ℚ_[p])) n hn z w h).trans (hp p)⟩

lemma actual_sha_class_iff (n : ℚ) (hn : n ≠ 0) (z : continuousFullCocycles n hn) :
    fullClassHom n hn z ∈ actualSha n hn ↔ EverywhereLocallyTrivial n hn z := by
  constructor
  · rintro ⟨w,hw,hwloc⟩
    exact (actual_local_triviality_class_invariant n hn w z hw).mp hwloc
  · intro hz; exact ⟨z,rfl,hz⟩

end ActualTwoDescentShaRepresentativeIndependence318
