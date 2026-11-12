module
public import ActualTwoDescentAlternatingCyclicPairing318
public section
noncomputable section
namespace ActualTwoDescentActualShaPrimary318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaDefinition318 ActualTwoDescentFullEllipticRepresentation318

def fullShaInclusion (n : ℚ) (hn : n ≠ 0) :
    Multiplicative (actualSha n hn) →* Multiplicative (groupCohomology.H1 (fullEllipticRep n hn)) where
  toFun x := Multiplicative.ofAdd (x.toAdd : groupCohomology.H1 (fullEllipticRep n hn))
  map_one' := rfl
  map_mul' x y := rfl

lemma actual_full_sha_inclusion_injective (n : ℚ) (hn : n ≠ 0) : Function.Injective (fullShaInclusion n hn) := by
  intro x y h
  exact Subtype.ext (congrArg Multiplicative.toAdd h)

/-- The ACTUAL full2-primary subgroup of genuine elliptic Sha, not its2-torsion subgroup. -/
abbrev actualShaPrimary (n : ℚ) (hn : n ≠ 0) := CommGroup.primaryComponent (Multiplicative (actualSha n hn)) 2

def primaryShaInclusion (n : ℚ) (hn : n ≠ 0) :
    actualShaPrimary n hn →* Multiplicative (groupCohomology.H1 (fullEllipticRep n hn)) :=
  (fullShaInclusion n hn).comp (actualShaPrimary n hn).subtype

lemma actual_primary_sha_inclusion_injective (n : ℚ) (hn : n ≠ 0) : Function.Injective (primaryShaInclusion n hn) := by
  intro x y h
  exact Subtype.ext (actual_full_sha_inclusion_injective n hn h)

lemma actual_sha_primary_is_two_group (n : ℚ) (hn : n ≠ 0) : IsPGroup 2 (actualShaPrimary n hn) :=
  CommGroup.primaryComponent.isPGroup

end ActualTwoDescentActualShaPrimary318
