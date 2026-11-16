module
public import ActualTwoDescentHigherKummerHom318
public section
noncomputable section
namespace ActualTwoDescentHigherKummerKernelForward318
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

open ActualTwoDescentGeometricDivisionTower318 ActualTwoDescentPowerValuedCocycles318
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherDivisionCocycle318
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentFullBoundaryHom318
open ActualTwoDescentActualEllipticFieldMap318

lemma actual_higher_kummer_zero_implies_divisible (n : F) (hn : n ≠ 0) (k : ℕ) (P : Point n)
    (h : higherKummerHom n hn k P=0) : ∃ R : Point n, (2^k) • R=P := by
  let Q := geometricDivision n hn (rationalPointMap n hn P) k
  have hQ : (2^k) • Q=rationalPointMap n hn P := actual_geometric_division_power n hn _ k
  have hz : divisionCocycle n hn k P Q hQ ∈ (powerBoundaryHom n hn k).range :=
    (QuotientAddGroup.eq_zero_iff _).mp h
  obtain ⟨T,hT⟩ := hz
  have he (σ : Gal) : halfDifference n hn T.val σ=halfDifference n hn Q σ :=
    congrArg (fun z : powerValuedCocycles n hn k => z.val.val σ) hT
  have hfix (σ : Gal) : galoisPointHom σ n hn (Q-T.val)=Q-T.val := by
    have hh := he σ
    dsimp [halfDifference] at hh
    rw [map_sub]
    calc
      _=(galoisPointHom σ n hn Q-Q)-(galoisPointHom σ n hn T.val-T.val)+(Q-T.val) := by abel
      _=Q-T.val := by rw [←hh,sub_self,zero_add]
  obtain ⟨R,hR⟩ := actual_fixed_point_rational n hn (Q-T.val) hfix
  refine ⟨R,?_⟩
  apply actual_elliptic_field_map_injective (algebraMap F Qbar) n hn
  change rationalPointMap n hn ((2^k) • R)=rationalPointMap n hn P
  rw [map_nsmul,hR,nsmul_sub,hQ]
  have ht : (2^k) • T.val=0 := T.property
  rw [ht,sub_zero]

end ActualTwoDescentHigherKummerKernelForward318
