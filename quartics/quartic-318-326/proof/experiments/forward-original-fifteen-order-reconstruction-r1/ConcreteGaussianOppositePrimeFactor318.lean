module
public import ConcreteGaussianPrimeOrder318
public section
noncomputable section
namespace ConcreteGaussianOppositePrimeFactor318
open SelectedQuotientOrders318 ConcretePadic318 SelectedEntryDenominatorDivisibility318
local instance : Fact (Nat.Prime 9649) := ⟨GaussianFixedRayConcretePrime318.rational_prime⟩
/-- New GENUINE opposite-order factor149, obtained from exact16R
coordinates and the actual quarter bound2384. The opposite order is NOT
asserted equal to149: a remaining power of2 is not resolved here. -/
theorem actual_factors : ∃ rho : ℚ_[9649],∃ hr : rho^2=2,
    order 9649 rho hr=2441 ∧
    order 9649 (-rho) (negative_root 9649 rho hr)∣2384 ∧
    149∣order 9649 (-rho) (negative_root 9649 rho hr) ∧
    Nat.Coprime (order 9649 rho hr) (order 9649 (-rho) (negative_root 9649 rho hr)) := by
  obtain ⟨rho,hr,he,hd,_,hcop⟩:=ConcreteGaussianPrimeOrder318.actual_order
  have hf : 149∣order 9649 (-rho) (negative_root 9649 rho hr) := by
    apply SelectedDenominatorPrimeFactor318.prime_factor 9649 (-rho)
      (negative_root 9649 rho hr) 2384 149 (by decide) (by decide) (by decide) hd
    simpa only [show 2384/149=16 from rfl] using ConcreteOriginalSixteenDenominator318.nondivisibility
  exact ⟨rho,hr,he,hd,hf,hcop⟩
end ConcreteGaussianOppositePrimeFactor318
