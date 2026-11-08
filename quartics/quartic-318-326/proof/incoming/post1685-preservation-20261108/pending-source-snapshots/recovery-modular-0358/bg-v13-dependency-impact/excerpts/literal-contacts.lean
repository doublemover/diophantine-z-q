module
public import FiniteContact318
public import HeightSeparation318
public import Mathlib.RingTheory.Coprime.Lemmas
public section
namespace ContactRadical318
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section

@[expose] def badPrimes : Finset ℕ := {2,3,5,7,11,13,17,37,41,73,109,359,439,2399,4801}
@[expose] def badProduct : ℕ := ∏p∈badPrimes,p

theorem bad_product_exact : badProduct=11185621387570686764517810 := by
  norm_num [badProduct,badPrimes]

theorem bad_product_bound : badProduct<2^84 := by
  rw [bad_product_exact]
  norm_num

/-- Primitive integer contact forms for (u:v), including infinity. -/
@[expose] def forms (u v:ℤ) : Fin 5→ℤ := ![v,u,u-v,u-2401*v,32*u+343*v]

/-- Actual finite odd-contact support, with the exact fixed exceptional primes removed. -/
@[expose] def contactPrimes (u v:ℤ) : Finset ℕ :=
  Finset.univ.biUnion (fun j:Fin 5 =>
    ((forms u v j).natAbs.primeFactors).filter (fun p=>p∉badPrimes ∧ Odd (padicValInt p (forms u v j))))

@[expose] def radical (u v:ℤ) : ℕ := ∏p∈contactPrimes u v,p

/-- The detector t=a/b maps to the actual homogeneous point (2a+b:a). -/
@[expose] def detectorPrimes (t:ℚ) : Finset ℕ := contactPrimes (2*t.num+t.den) t.num
@[expose] def detectorRadical (t:ℚ) : ℕ := radical (2*t.num+t.den) t.num

