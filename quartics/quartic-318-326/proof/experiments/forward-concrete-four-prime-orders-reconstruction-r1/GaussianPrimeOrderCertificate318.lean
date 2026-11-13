module
public import ConcreteGaussianOppositePrimeFactor318
public section
noncomputable section
namespace GaussianPrimeOrderCertificate318
open SelectedQuotientOrders318 SelectedReductionOrder318 ConcretePadic318
open SelectedEntryDenominatorDivisibility318
/-- Finite arithmetic data only. The concrete successors discharge every field.
No prime distribution, chosen p-adic root or actual order is part of this input. -/
structure Data (p : ℕ) where
  a : ℤ
  b : ℤ
  m : ℕ
  n : ℕ
  ray : GaussianRayQuadratic318.Ray p a b
  a7 : a%7=1
  b7 : b%7=3
  mod8 : p%8=1
  notTwo : p≠2
  notSevenSquare : ¬p∣49
  z : ZMod p
  t : ZMod p
  z8 : z^8= -1
  t4 : t^4=2
  minus : GaussianNeighborNorms318.minus a b=64*m
  plus : GaussianNeighborNorms318.plus a b=4*n
  total : 64*m+4*n=2*(p+1)
  mPrime : m.Prime
  nPrime : n.Prime
  denominator : ¬p∣multipleDenominator 16
  coprime : Nat.Coprime n (16*m)
variable (p : ℕ) [Fact p.Prime]
lemma plus_root (D : Data p) : ∃ rho : ℚ_[p], ∃ hr : rho^2=2,
    pointCount p rho hr=4*D.n := by
  obtain ⟨rho,hr⟩ := SelectedRayEmbeddings318.square_root p D.mod8
  have hc := CanonicalSelectedCounts318.actual_count p rho hr D.a D.b D.ray
    D.a7 D.b7 (CanonicalJacobiNorm318.canonical_from_ray p D.a D.b D.ray)
  rw [D.minus,D.plus] at hc
  rcases hc with hm|hn
  · have hs := ActualConjugateCounts318.count_sum_from_ray p rho hr D.a D.b
      D.ray D.a7 D.b7
    refine ⟨-rho,negative_root p rho hr,?_⟩
    have ht := D.total
    omega
  · exact ⟨rho,hr,hn⟩
/-- Produced native orders, not residue group orders. The opposite 2-part remains open. -/
theorem actual (D : Data p) : ∃ rho : ℚ_[p], ∃ hr : rho^2=2,
    order p rho hr=D.n ∧
    order p (-rho) (negative_root p rho hr)∣16*D.m ∧
    D.m∣order p (-rho) (negative_root p rho hr) ∧
    Nat.Coprime (order p rho hr) (order p (-rho) (negative_root p rho hr)) := by
  obtain ⟨rho,hr,hc⟩ := plus_root p D
  have hs := ActualConjugateCounts318.count_sum_from_ray p rho hr D.a D.b D.ray D.a7 D.b7
  have hc' : pointCount p (-rho) (negative_root p rho hr)=64*D.m := by
    have ht := D.total
    omega
  have hn := SelectedQuarterOrder318.actual_order_dvd_quarter p rho hr
    D.notTwo D.notSevenSquare D.z D.t D.z8 D.t4
  rw [hc] at hn
  have hn' : order p rho hr∣D.n := by simpa using hn
  have he := SelectedExactOrderCertificates318.prime_upper p rho hr D.n D.nPrime hn'
  have hd := SelectedQuarterOrder318.actual_order_dvd_quarter p (-rho)
    (negative_root p rho hr) D.notTwo D.notSevenSquare D.z D.t D.z8 D.t4
  rw [hc'] at hd
  have hd' : order p (-rho) (negative_root p rho hr)∣16*D.m := by
    have hdiv : 64*D.m/4=16*D.m := by omega
    simpa only [hdiv] using hd
  have hfactor : D.m∣order p (-rho) (negative_root p rho hr) := by
    apply SelectedDenominatorPrimeFactor318.prime_factor p (-rho)
      (negative_root p rho hr) (16*D.m) D.m (by have := D.mPrime.pos; omega)
      D.mPrime (dvd_mul_left _ _) hd'
    have hdiv : 16*D.m/D.m=16 := Nat.mul_div_cancel 16 D.mPrime.pos
    simpa only [hdiv] using D.denominator
  refine ⟨rho,hr,he,hd',hfactor,?_⟩
  rw [he]
  exact D.coprime.of_dvd_right hd'
end GaussianPrimeOrderCertificate318
