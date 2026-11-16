module
public import ActualTwoDescentHigherFullKernel318
public section
noncomputable section
namespace ActualTwoDescentHigherFullLifting318
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
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherFullClassMap318 ActualTwoDescentFullBoundaryHom318

/-- Every genuinely continuous full elliptic H1 class killed by2^k lifts to an actual E[2^k]-valued crossed cocycle. -/
theorem actual_higher_full_lift (n : F) (hn : n ≠ 0) (k : ℕ) (z : continuousFullCocycles n hn)
    (hz : (2^k) • fullClassHom n hn z=0) :
    ∃ w : powerValuedCocycles n hn k, powerFullClass n hn k w=fullClassHom n hn z := by
  have hzero : fullClassHom n hn ((2^k) • z)=0 := by rw [map_nsmul]; exact hz
  obtain ⟨Q,hQ⟩ := (actual_full_class_zero n hn ((2^k) • z)).mp hzero
  let R := geometricDivision n hn Q k
  have hR : (2^k) • R=Q := actual_geometric_division_power n hn Q k
  let w : powerValuedCocycles n hn k := ⟨z-fullBoundary n hn R,by
    intro σ
    change (2^k) • (z.val σ-halfDifference n hn R σ)=0
    rw [nsmul_sub,←actual_difference_nsmul,hR]
    exact sub_eq_zero.mpr (hQ σ)⟩
  refine ⟨w,?_⟩
  change fullClassHom n hn (z-fullBoundary n hn R)=fullClassHom n hn z
  rw [map_sub,actual_full_boundary_zero,sub_zero]

/-- Surjectivity is restricted precisely to actual continuous full classes and their actual2^k-torsion. -/
theorem actual_higher_full_range (n : F) (hn : n ≠ 0) (k : ℕ) (x : H1 (fullEllipticRep n hn)) :
    x ∈ (higherFullClass n hn k).range ↔ x ∈ continuousFullHOne n hn ∧ (2^k) • x=0 := by
  constructor
  · rintro ⟨w,rfl⟩
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective w
    exact ⟨⟨z.val,rfl⟩,actual_higher_full_annihilated n hn k _⟩
  · rintro ⟨⟨z,rfl⟩,hz⟩
    obtain ⟨w,hw⟩ := actual_higher_full_lift n hn k z hz
    exact ⟨powerClass n hn k w,hw⟩

end ActualTwoDescentHigherFullLifting318
