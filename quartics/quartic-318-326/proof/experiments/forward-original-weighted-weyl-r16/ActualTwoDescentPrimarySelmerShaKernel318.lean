module
public import ActualTwoDescentPrimarySelmerShaSurjectivity318
public section
noncomputable section
namespace ActualTwoDescentPrimarySelmerShaKernel318
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

open ActualTwoDescentPrimarySelmerToSha318 ActualTwoDescentRationalPrimaryTransition318
open ActualTwoDescentActualPrimaryRationalImage318

lemma actual_rational_primary_full_zero (n : ℚ) (hn : n ≠ 0) (k : ℕ) (P : Point n) :
    primarySelmerToSha n hn (rationalPrimaryHom n hn k P)=0 := by
  apply Subtype.ext; apply Subtype.ext
  change primaryFullClass n hn (powerIntoPrimaryHOne n hn k (higherKummerHom n hn k P))=0
  rw [actual_primary_full_finite_level,actual_higher_full_kummer_zero]

/-- Actual full primary Selmer-to-Sha kernel is the independently defined rational primary image. -/
theorem actual_primary_selmer_sha_kernel (n : ℚ) (hn : n ≠ 0) :
    (primarySelmerToSha n hn).ker=rationalPrimaryImage n hn := by
  ext x
  change primarySelmerToSha n hn x=0 ↔ _
  constructor
  · intro hx
    obtain ⟨k,y,hy⟩ := actual_primary_selmer_finite_level n hn x
    have he : higherSelmerIntoPrimary n hn k y=x := Subtype.ext hy
    have hz : primaryFullClass n hn x.val=0 := congrArg
      (fun g : Additive (ActualTwoDescentActualShaPrimary318.actualShaPrimary n hn) => g.toMul.val.toAdd.val) hx
    rw [←hy,actual_primary_full_finite_level] at hz
    obtain ⟨P,hP⟩ := (actual_higher_full_kernel n hn k y.val).mp hz
    refine ⟨k,P,?_⟩
    apply Subtype.ext
    exact (congrArg (powerIntoPrimaryHOne n hn k) hP).trans hy
  · rintro ⟨k,P,rfl⟩
    exact actual_rational_primary_full_zero n hn k P

end ActualTwoDescentPrimarySelmerShaKernel318
