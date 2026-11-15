module
public import ActualTwoDescentFamilyReciprocity318
public section
noncomputable section
namespace ActualTwoDescentTwistDomain318
open ActualTwoDescentPrimeFamily318 ActualTwoDescentFamilyProducts318
open scoped BigOperators
set_option maxHeartbeats 16000000

abbrev Support (m : ℕ) := {p : ℕ // p ∈ m.primeFactors}
def supportPrime (m : ℕ) (i : Support m) : ℕ := i.val
instance support_prime (m : ℕ) (i : Support m) : Fact (supportPrime m i).Prime :=
  ⟨Nat.prime_of_mem_primeFactors i.property⟩

/-- Both actual squarefree twist parameters and their literal congruence
domain. This record deliberately contains no rational-point conclusion. -/
structure TwistDomain (β θ n : ℕ) : Prop where
  positive : 0 < n
  squarefree : Squarefree n
  twisted_positive : 0 < n*θ
  twisted_squarefree : Squarefree (n*θ)
  residue : (n : ZMod 12)=11
  twisted_residue : ((n*θ : ℕ) : ZMod 12)=11
  beta_divides : β ∣ n

/-- The actual original prime support and all symbol requirements produce
arbitrarily large twist parameters. No suitable auxiliary family, CRT unit,
squarefree parameter, or congruence-domain witness is assumed as input. -/
theorem actual_twist_domain (β θ : ℕ) (hsq : Squarefree (β*θ))
    (hβ : (β : ZMod 12)=5) (hθ : (θ : ZMod 12)=1)
    (oldBits : ℕ → Support (β*θ) → Bool) (newBits : ℕ → ℕ → Bool)
    (forbidden : Finset ℕ) (N d : ℕ) :
    ∃ F : PrimeFamily (supportPrime (β*θ)) oldBits newBits
      (fun i => decide (i=d)) forbidden N (d+1),
      TwistDomain β θ (β*multiplier F) ∧
      N < β*multiplier F ∧ N < (β*multiplier F)*θ ∧
      Nat.Coprime (multiplier F) (β*θ) := by
  classical
  have hc : Nat.Coprime (β*θ) 12 := by
    apply (ZMod.isUnit_iff_coprime (β*θ) 12).mp
    simpa only [Nat.cast_mul,hβ,hθ,mul_one] using
      (ZMod.unitOfCoprime 5 (by decide : Nat.Coprime 5 12)).isUnit
  have hdc : Function.Injective (supportPrime (β*θ)) := by
    intro i j h
    exact Subtype.ext h
  have hpc : ∀ i : Support (β*θ), Nat.Coprime (supportPrime (β*θ) i) 12 := by
    intro i
    exact hc.of_dvd_left (Nat.dvd_of_mem_primeFactors i.property)
  have hp2 : ∀ i : Support (β*θ), supportPrime (β*θ) i ≠ 2 := by
    intro i he
    have hh := hpc i
    rw [he] at hh
    norm_num at hh
  obtain ⟨F⟩ := actual_finite_family (supportPrime (β*θ)) hdc hpc hp2
    oldBits newBits (fun i => decide (i=d)) forbidden N (d+1)
  have cover : ∀ q : ℕ, q.Prime → q ∣ β*θ → ∃ i : Support (β*θ), supportPrime (β*θ) i=q := by
    intro q hq hdiv
    exact ⟨⟨q,(Nat.mem_primeFactors_of_ne_zero hsq.ne_zero).mpr ⟨hq,hdiv⟩⟩,rfl⟩
  have hcop := actual_multiplier_coprime F (β*θ) cover
  have hm := actual_multiplier_squarefree F
  have htotal : Squarefree ((β*θ)*multiplier F) :=
    (Nat.squarefree_mul hcop.symm).mpr ⟨hsq,hm⟩
  have htw : Squarefree ((β*multiplier F)*θ) := by
    convert htotal using 1 <;> ring
  have hn : Squarefree (β*multiplier F) := htw.of_mul_left
  have hres := actual_multiplier_residue d F
  have hnres : ((β*multiplier F : ℕ) : ZMod 12)=11 := by
    rw [Nat.cast_mul,hβ,hres]
    norm_num
  have htres : (((β*multiplier F)*θ : ℕ) : ZMod 12)=11 := by
    rw [Nat.cast_mul,hnres,hθ,mul_one]
  have hβpos : 0 < β := Nat.pos_of_ne_zero hsq.of_mul_left.ne_zero
  have hθpos : 0 < θ := Nat.pos_of_ne_zero hsq.of_mul_right.ne_zero
  have hmp := actual_multiplier_positive F
  have hlower := F.large (Fin.last d)
  have hprod : F.value (Fin.last d) ≤ multiplier F := by
    apply Nat.le_of_dvd hmp
    exact Finset.dvd_prod_of_mem F.value (Finset.mem_univ (Fin.last d))
  have hN : N < F.value (Fin.last d) := lt_of_le_of_lt (le_max_left _ _) hlower
  have hmle : multiplier F ≤ β*multiplier F := by
    simpa only [one_mul] using
      (Nat.mul_le_mul_right (multiplier F) (Nat.succ_le_iff.mpr hβpos))
  have hNn : N < β*multiplier F := lt_of_lt_of_le (lt_of_lt_of_le hN hprod) hmle
  have hnle : β*multiplier F ≤ (β*multiplier F)*θ := by
    simpa only [mul_one] using
      (Nat.mul_le_mul_left (β*multiplier F) (Nat.succ_le_iff.mpr hθpos))
  refine ⟨F,⟨Nat.mul_pos hβpos hmp,hn,
    Nat.mul_pos (Nat.mul_pos hβpos hmp) hθpos,htw,hnres,htres,
    dvd_mul_right β (multiplier F)⟩,hNn,lt_of_lt_of_le hNn hnle,hcop⟩

end ActualTwoDescentTwistDomain318
