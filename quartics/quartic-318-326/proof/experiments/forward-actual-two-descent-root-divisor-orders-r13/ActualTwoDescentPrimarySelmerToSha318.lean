module
public import ActualTwoDescentActualPrimaryRationalImage318
public section
noncomputable section
namespace ActualTwoDescentPrimarySelmerToSha318
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
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherKummerHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentPrimaryGeometricBoundary318 ActualTwoDescentFiniteLevelIntoPrimary318
open ActualTwoDescentPrimaryFullClass318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerIntoPrimary318
open ActualTwoDescentPrimarySelmerFiniteLevels318 ActualTwoDescentHigherRationalImage318

open ActualTwoDescentActualShaDefinition318 ActualTwoDescentActualShaPrimary318

/-- Actual full primary Selmer-to-Sha map, landing in the independently defined actual full primary Sha subgroup. -/
def primarySelmerToSha (n : ℚ) (hn : n ≠ 0) : actualPrimarySelmer n hn →+ Additive (actualShaPrimary n hn) where
  toFun x := by
    let a := primaryFullClass n hn x.val
    have ha : a ∈ actualSha n hn := (actual_primary_selmer_iff_sha n hn x.val).mp x.property
    exact Additive.ofMul ⟨Multiplicative.ofAdd ⟨a,ha⟩,by
      obtain ⟨k,hk⟩ := ((actual_primary_full_range n hn a).mp ⟨x.val,rfl⟩).2
      exact ⟨k,Subtype.ext hk⟩⟩
  map_zero' := by apply Subtype.ext; apply Subtype.ext; exact map_zero _
  map_add' x y := by apply Subtype.ext; apply Subtype.ext; exact map_add _ x.val y.val

lemma actual_primary_selmer_sha_value (n : ℚ) (hn : n ≠ 0) (x : actualPrimarySelmer n hn) :
    ((primarySelmerToSha n hn x).toMul.val.toAdd : H1 (fullEllipticRep n hn))=primaryFullClass n hn x.val := rfl

end ActualTwoDescentPrimarySelmerToSha318
