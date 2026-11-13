module
public import GaussianPrimeOrderCertificate318
public import AdditionalSixteenDenominators318
public section
noncomputable section
namespace ConcretePrimeRay387089318
open GaussianPrimeOrderCertificate318 SelectedQuotientOrders318 ConcretePadic318
lemma prime : Nat.Prime 387089 := by norm_num
local instance : Fact (Nat.Prime 387089) := ⟨prime⟩
def data : Data 387089 where
  a := 617
  b := 80
  m := 6029
  n := 97081
  ray := by norm_num [GaussianRayQuadratic318.Ray]
  a7 := by norm_num
  b7 := by norm_num
  mod8 := by norm_num
  notTwo := by decide
  notSevenSquare := by decide
  z := 9530
  t := 77299
  z8 := by norm_num
  t4 := by norm_num
  minus := by norm_num [GaussianNeighborNorms318.minus,GaussianNeighborNorms318.norm]
  plus := by norm_num [GaussianNeighborNorms318.plus,GaussianNeighborNorms318.norm]
  total := by norm_num
  mPrime := by norm_num
  nPrime := by norm_num
  denominator := AdditionalSixteenDenominators318.nondiv_387089
  coprime := by decide
/-- A genuine single-prime native two-root witness, not an original fifteen-position tuple. -/
theorem actual : ∃ rho : ℚ_[387089], ∃ hr : rho^2=2,
    order 387089 rho hr=97081 ∧
    order 387089 (-rho) (negative_root 387089 rho hr)∣96464 ∧
    6029∣order 387089 (-rho) (negative_root 387089 rho hr) ∧
    Nat.Coprime (order 387089 rho hr) (order 387089 (-rho) (negative_root 387089 rho hr)) := by
  simpa only [data,show 16*6029=96464 from rfl] using GaussianPrimeOrderCertificate318.actual 387089 data
end ConcretePrimeRay387089318
