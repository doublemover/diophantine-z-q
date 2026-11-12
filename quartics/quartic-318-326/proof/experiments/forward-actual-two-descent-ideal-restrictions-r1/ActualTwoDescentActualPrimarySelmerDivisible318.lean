module
public import ActualTwoDescentActualShaPrimaryDivision318
public section
noncomputable section
namespace ActualTwoDescentActualPrimarySelmerDivisible318
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

open ActualTwoDescentPrimarySelmerToSha318 ActualTwoDescentPrimarySelmerShaSurjectivity318
open ActualTwoDescentPrimarySelmerShaKernel318 ActualTwoDescentActualPrimaryRationalImage318
open ActualTwoDescentRationalPrimaryDivision318 ActualTwoDescentActualShaPrimaryDivision318
open ActualTwoDescentActualShaReducedDuality318 ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- With the genuine global reduced pairing explicitly supplied, the ACTUAL full primary Selmer group is2-divisible: lift a half from actual Sha, then correct by a half in the actual rational image. -/
theorem actual_primary_selmer_two_surjective (n : ℚ) (hn : n ≠ 0)
    (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) (hdual : ActualReducedDuality n hn) :
    Function.Surjective (nsmulAddMonoidHom (α:=actualPrimarySelmer n hn) 2) := by
  intro x
  obtain ⟨a,ha⟩ := actual_sha_primary_two_surjective_of_duality n hn hf hb hS hdual (primarySelmerToSha n hn x)
  obtain ⟨y,hy⟩ := actual_primary_selmer_sha_surjective n hn a
  have hm : x-2 • y ∈ rationalPrimaryImage n hn := by
    rw [←actual_primary_selmer_sha_kernel]
    change primarySelmerToSha n hn (x-2 • y)=0
    rw [map_sub,map_nsmul,hy,ha,sub_self]
  obtain ⟨u,hu⟩ := actual_rational_primary_two_surjective n hn ⟨x-2 • y,hm⟩
  refine ⟨y+u.val,?_⟩
  have huv : 2 • u.val=x-2 • y := congrArg Subtype.val hu
  change 2 • (y+u.val)=x
  rw [nsmul_add,huv]
  abel

end ActualTwoDescentActualPrimarySelmerDivisible318
