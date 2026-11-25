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

 theorem mem_contactPrimes (u v:ℤ) (p:ℕ) : p∈contactPrimes u v ↔
    ∃j:Fin 5,p∈(forms u v j).natAbs.primeFactors ∧ p∉badPrimes ∧ Odd (padicValInt p (forms u v j)) := by
  simp only [contactPrimes,Finset.mem_biUnion,Finset.mem_univ,Finset.mem_filter,true_and]

 theorem member_prime (u v:ℤ) (p:ℕ) (hp:p∈contactPrimes u v) : p.Prime := by
  obtain ⟨j,hj,_,_⟩:=(mem_contactPrimes u v p).mp hp
  exact (Nat.mem_primeFactors.mp hj).1

 theorem radical_pos (u v:ℤ) : 0<radical u v := by
  exact Finset.prod_pos (fun p hp=>(member_prime u v p hp).pos)

 theorem radical_power_dvd (u v N:ℤ) (k:ℕ)
    (hdiv:∀p∈contactPrimes u v,(p:ℤ)^k∣N) : (radical u v:ℤ)^k∣N := by
  have hc : (contactPrimes u v : Set ℕ).Pairwise (fun p q=>IsCoprime ((p:ℤ)^k) ((q:ℤ)^k)) := by
    intro p hp q hq hpq
    have hcop : Nat.Coprime p q := (member_prime u v p hp).coprime_iff_not_dvd.mpr (by
      intro hd
      exact hpq ((Nat.prime_dvd_prime_iff_eq (member_prime u v p hp) (member_prime u v q hq)).mp hd))
    have hi : IsCoprime (p:ℤ) (q:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcop)
    exact hi.pow
  have hh:=Finset.prod_dvd_of_coprime hc hdiv
  simpa only [radical,Nat.cast_prod,Finset.prod_pow] using hh

 theorem radical_power_le (u v N:ℤ) (hN:N≠0) (k:ℕ)
    (hdiv:∀p∈contactPrimes u v,(p:ℤ)^k∣N) : (radical u v:ℝ)^k≤|(N:ℝ)| := by
  have hh:=Int.natAbs_le_of_dvd_ne_zero (radical_power_dvd u v N k hdiv) hN
  simp only [Int.natAbs_pow,Int.natAbs_natCast] at hh
  have hhR : (radical u v:ℝ)^k≤(N.natAbs:ℝ) := by exact_mod_cast hh
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hhR

end
end ContactRadical318
#print axioms ContactRadical318.radical_power_dvd
#print axioms ContactRadical318.radical_power_le
