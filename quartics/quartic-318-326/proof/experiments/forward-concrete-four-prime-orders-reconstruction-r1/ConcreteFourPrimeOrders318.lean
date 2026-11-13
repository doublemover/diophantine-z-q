module
public import ConcretePrimeRay95441318
public import ConcretePrimeRay387089318
public import ConcretePrimeRay1473041318
public section
noncomputable section
namespace ConcreteFourPrimeOrders318
open SelectedQuotientOrders318 ConcretePadic318
/-- Four independently constructed primes. This index is NOT Fin3×Fin5. -/
def primeValue (i : Fin 4) : ℕ := ![9649,95441,387089,1473041] i
def oddFactor (i : Fin 4) : ℕ := ![149,1493,6029,23053] i
def primeOrder (i : Fin 4) : ℕ := ![2441,23833,97081,367673] i
lemma isPrime (i : Fin 4) : (primeValue i).Prime := by
  fin_cases i <;> norm_num [primeValue]
instance primeFact (i : Fin 4) : Fact (primeValue i).Prime := ⟨isPrime i⟩
theorem family (i : Fin 4) : ∃ rho : ℚ_[primeValue i], ∃ hr : rho^2=2,
    order (primeValue i) rho hr=primeOrder i ∧
    order (primeValue i) (-rho) (negative_root _ rho hr)∣16*oddFactor i ∧
    oddFactor i∣order (primeValue i) (-rho) (negative_root _ rho hr) ∧
    Nat.Coprime (order (primeValue i) rho hr)
      (order (primeValue i) (-rho) (negative_root _ rho hr)) := by
  fin_cases i
  · exact ConcreteGaussianOppositePrimeFactor318.actual_factors
  · exact ConcretePrimeRay95441318.actual
  · exact ConcretePrimeRay387089318.actual
  · exact ConcretePrimeRay1473041318.actual
def root (i : Fin 4) : {rho : ℚ_[primeValue i] // rho^2=2} :=
  ⟨(family i).choose,(family i).choose_spec.choose⟩
def primary (i : Fin 4) : ℕ := order (primeValue i) (root i).val (root i).property
def opposite (i : Fin 4) : ℕ := order (primeValue i) (-(root i).val)
  (negative_root _ (root i).val (root i).property)
lemma primary_eq (i : Fin 4) : primary i=primeOrder i :=
  (family i).choose_spec.choose_spec.1
lemma opposite_dvd (i : Fin 4) : opposite i∣16*oddFactor i :=
  (family i).choose_spec.choose_spec.2.1
lemma factor_dvd (i : Fin 4) : oddFactor i∣opposite i :=
  (family i).choose_spec.choose_spec.2.2.1
end ConcreteFourPrimeOrders318
