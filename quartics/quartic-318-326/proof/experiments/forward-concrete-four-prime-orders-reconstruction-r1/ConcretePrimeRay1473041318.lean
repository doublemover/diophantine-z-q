module
public import GaussianPrimeOrderCertificate318
public import AdditionalSixteenDenominators318
public section
noncomputable section
namespace ConcretePrimeRay1473041318
open GaussianPrimeOrderCertificate318 SelectedQuotientOrders318 ConcretePadic318
lemma prime : Nat.Prime 1473041 := by norm_num
local instance : Fact (Nat.Prime 1473041) := ⟨prime⟩
def data : Data 1473041 where
  a := -1175
  b := 304
  m := 23053
  n := 367673
  ray := by norm_num [GaussianRayQuadratic318.Ray]
  a7 := by norm_num
  b7 := by norm_num
  mod8 := by norm_num
  notTwo := by decide
  notSevenSquare := by decide
  z := 11073
  t := 396496
  z8 := by norm_num
  t4 := by norm_num
  minus := by norm_num [GaussianNeighborNorms318.minus,GaussianNeighborNorms318.norm]
  plus := by norm_num [GaussianNeighborNorms318.plus,GaussianNeighborNorms318.norm]
  total := by norm_num
  mPrime := by norm_num
  nPrime := by norm_num
  denominator := AdditionalSixteenDenominators318.nondiv_1473041
  coprime := by decide
/-- A genuine single-prime native two-root witness, not an original fifteen-position tuple. -/
theorem actual : ∃ rho : ℚ_[1473041], ∃ hr : rho^2=2,
    order 1473041 rho hr=367673 ∧
    order 1473041 (-rho) (negative_root 1473041 rho hr)∣368848 ∧
    23053∣order 1473041 (-rho) (negative_root 1473041 rho hr) ∧
    Nat.Coprime (order 1473041 rho hr) (order 1473041 (-rho) (negative_root 1473041 rho hr)) := by
  simpa only [data,show 16*23053=368848 from rfl] using GaussianPrimeOrderCertificate318.actual 1473041 data
end ConcretePrimeRay1473041318
