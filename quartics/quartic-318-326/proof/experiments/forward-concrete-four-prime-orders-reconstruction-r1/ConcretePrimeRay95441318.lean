module
public import GaussianPrimeOrderCertificate318
public import AdditionalSixteenDenominators318
public section
noncomputable section
namespace ConcretePrimeRay95441318
open GaussianPrimeOrderCertificate318 SelectedQuotientOrders318 ConcretePadic318
lemma prime : Nat.Prime 95441 := by norm_num
local instance : Fact (Nat.Prime 95441) := ⟨prime⟩
def data : Data 95441 where
  a := -55
  b := 304
  m := 1493
  n := 23833
  ray := by norm_num [GaussianRayQuadratic318.Ray]
  a7 := by norm_num
  b7 := by norm_num
  mod8 := by norm_num
  notTwo := by decide
  notSevenSquare := by decide
  z := 11939
  t := 23653
  z8 := by norm_num
  t4 := by norm_num
  minus := by norm_num [GaussianNeighborNorms318.minus,GaussianNeighborNorms318.norm]
  plus := by norm_num [GaussianNeighborNorms318.plus,GaussianNeighborNorms318.norm]
  total := by norm_num
  mPrime := by norm_num
  nPrime := by norm_num
  denominator := AdditionalSixteenDenominators318.nondiv_95441
  coprime := by decide
/-- A genuine single-prime native two-root witness, not an original fifteen-position tuple. -/
theorem actual : ∃ rho : ℚ_[95441], ∃ hr : rho^2=2,
    order 95441 rho hr=23833 ∧
    order 95441 (-rho) (negative_root 95441 rho hr)∣23888 ∧
    1493∣order 95441 (-rho) (negative_root 95441 rho hr) ∧
    Nat.Coprime (order 95441 rho hr) (order 95441 (-rho) (negative_root 95441 rho hr)) := by
  simpa only [data,show 16*1493=23888 from rfl] using GaussianPrimeOrderCertificate318.actual 95441 data
end ConcretePrimeRay95441318
