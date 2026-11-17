module
public import ActualTwoDescentFiniteFactorPrimaryVanishing318
public section
noncomputable section
namespace ActualTwoDescentRankOneRationalCoordinates318
set_option maxHeartbeats 16000000
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

open ActualTwoDescentActualPrimaryRationalImage318 ActualTwoDescentRationalPrimaryDivision318
open ActualTwoDescentFullPrimarySelmerTorsion318 ActualTwoDescentPrimaryAllRoots318


open ActualTwoDescentPrimaryAllRoots318 ActualTwoDescentFullPrimarySelmerTorsion318

open ActualTwoDescentRestrictedRationalPrimaryImage318
open ActualTwoDescentRestrictedRationalPrimaryDivision318
open ActualTwoDescentFiniteFactorPrimaryVanishing318

def rankOneGenerator (n : ℚ) {T : Type} [AddCommGroup T]
    (e : Point n ≃+ ℤ × T) : Point n := e.symm (1,0)

def rankOneFiniteMap (n : ℚ) {T : Type} [AddCommGroup T]
    (e : Point n ≃+ ℤ × T) : T →+ Point n where
  toFun t := e.symm (0,t)
  map_zero' := e.symm.map_zero
  map_add' t u := e.symm.map_add (0,t) (0,u)

lemma actual_rank_one_point_split (n : ℚ) {T : Type} [AddCommGroup T]
    (e : Point n ≃+ ℤ × T) (P : Point n) :
    P=(e P).1 • rankOneGenerator n e+rankOneFiniteMap n e (e P).2 := by
  apply e.injective
  simp [rankOneGenerator,rankOneFiniteMap,map_add,map_zsmul,zsmul_eq_mul]

lemma actual_rank_one_primary_coordinate (n : ℚ) (hn : n ≠ 0)
    {T : Type} [AddCommGroup T] [Finite T] (e : Point n ≃+ ℤ × T) (k : ℕ) (P : Point n) :
    rationalPrimaryHom n hn k P=(e P).1 • rationalPrimaryHom n hn k (rankOneGenerator n e) := by
  conv_lhs => rw [actual_rank_one_point_split n e P]
  rw [map_add,map_zsmul,actual_finite_factor_primary_zero n hn (rankOneFiniteMap n e),add_zero]

end ActualTwoDescentRankOneRationalCoordinates318
