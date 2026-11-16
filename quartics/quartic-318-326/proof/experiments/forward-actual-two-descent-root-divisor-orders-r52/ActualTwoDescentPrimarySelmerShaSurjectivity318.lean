module
public import ActualTwoDescentPrimarySelmerToSha318
public section
noncomputable section
namespace ActualTwoDescentPrimarySelmerShaSurjectivity318
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

open ActualTwoDescentActualShaDefinition318 ActualTwoDescentActualShaPrimary318 ActualTwoDescentPrimarySelmerToSha318

lemma actual_primary_selmer_sha_surjective (n : ℚ) (hn : n ≠ 0) : Function.Surjective (primarySelmerToSha n hn) := by
  intro x
  let a : H1 (fullEllipticRep n hn) := x.toMul.val.toAdd.val
  have hSha : a ∈ actualSha n hn := x.toMul.val.toAdd.property
  obtain ⟨z,hz,hlocal⟩ := hSha
  have hc : a ∈ continuousFullHOne n hn := ⟨z,hz⟩
  obtain ⟨k,hk⟩ := x.toMul.property
  have hka : (2^k) • a=0 := congrArg (fun g : Multiplicative (actualSha n hn) => g.toAdd.val) hk
  obtain ⟨w,hw⟩ := (actual_primary_full_range n hn a).mpr ⟨hc,k,hka⟩
  have hm : w ∈ actualPrimarySelmer n hn := (actual_primary_selmer_iff_sha n hn w).mpr (by rw [hw]; exact ⟨z,hz,hlocal⟩)
  refine ⟨⟨w,hm⟩,?_⟩
  apply Subtype.ext; apply Subtype.ext
  exact hw

end ActualTwoDescentPrimarySelmerShaSurjectivity318
