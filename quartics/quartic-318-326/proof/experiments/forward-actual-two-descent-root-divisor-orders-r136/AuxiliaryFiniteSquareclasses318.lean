module
public import AuxiliaryLocalUnitClass318
public import AuxiliaryPrimeCRT318
public section
noncomputable section
namespace AuxiliaryFiniteSquareclasses318
open scoped BigOperators

/-- Actual local unit data on a finite prime set produce an auxiliary prime
and nonzero square multipliers at every specified place. Residues, CRT
coprimality and the prime are constructed. The family outside S is unused. -/
theorem prime_preserving_units (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ p∈S,p.Prime) (σ : ℤ) (hσ : σ=1 ∨ σ= -1)
    (u : ∀ p [Fact p.Prime], ℤ_[p])
    (hu : ∀ p (hp : p∈S), letI : Fact p.Prime := ⟨hS p hp⟩; ‖u p‖=1)
    (N : ℕ) :
    ∃ q : ℕ, N<q ∧ q.Prime ∧ ∀ p (hp : p∈S),
      letI : Fact p.Prime := ⟨hS p hp⟩;
      ∃ s : ℚ_[p], s≠0 ∧
        ((σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ):ℤ):ℚ_[p])=
          (p:ℚ_[p])^α p*(u p:ℚ_[p])*s^2 := by
  classical
  let k : ℕ → ℕ := fun p => if p=2 then 3 else 1
  let E : ℕ → ℤ := fun p => σ*((∏ r∈S.erase p,r^α r):ℕ)
  have hk (p : ℕ) : 0<k p := by dsimp only [k]; split_ifs <;> omega
  have hk2 (p : ℕ) (hp : p=2) : 3≤k p := by simp [k,hp]
  have hchoices : ∀ p : ℕ, ∃ n : ℕ, ∀ hp : p∈S,
      letI : Fact p.Prime := ⟨hS p hp⟩;
      ¬p∣n ∧ ∀ m : ℤ, (p:ℤ)^k p∣m-(n:ℤ) →
        ∃ s : ℚ_[p], s≠0 ∧ (E p:ℚ_[p])*(m:ℚ_[p])=(u p:ℚ_[p])*s^2 := by
    intro p
    by_cases hp : p∈S
    · letI : Fact p.Prime := ⟨hS p hp⟩
      obtain ⟨n,hn,htrans⟩ := AuxiliaryLocalUnitClass318.local_unit_class
        p (u p) (hu p hp) (E p)
        (AuxiliaryLocalUnitClass318.signed_complement_unit S α hS p hp σ hσ)
        (k p) (hk p) (hk2 p)
      exact ⟨n,fun _ => ⟨hn,htrans⟩⟩
    · exact ⟨0,fun h => False.elim (hp h)⟩
  choose a ha using hchoices
  have hm : ∀ p∈S,p^k p≠0 := fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  have hpair : Set.Pairwise S (fun p q => (p^k p).Coprime (q^k q)) := by
    intro p hp q hq hpq
    have hnot : ¬p∣q := by
      intro hd
      exact hpq (((Nat.dvd_prime (hS q hq)).mp hd).resolve_left (hS p hp).ne_one)
    exact (((hS p hp).coprime_iff_not_dvd.mpr hnot).pow_left _).pow_right _
  have hunit : ∀ p∈S,(a p).Coprime (p^k p) := by
    intro p hp
    exact ((hS p hp).coprime_iff_not_dvd.mpr (ha p hp).1).symm.pow_right _
  obtain ⟨q,hN,hq,hcong,_⟩ := AuxiliaryPrimeCRT318.prime_for_unit_residues
    S a (fun p => p^k p) hm hpair hunit N
  refine ⟨q,hN,hq,?_⟩
  intro p hp
  letI : Fact p.Prime := ⟨hS p hp⟩
  have hd : (p:ℤ)^k p∣(q:ℤ)-(a p:ℤ) := by
    simpa only [Nat.cast_pow] using (hcong p hp).symm.dvd
  obtain ⟨s,hs,he⟩ := (ha p hp).2 (q:ℤ) hd
  have heQ : (E p:ℚ_[p])*(q:ℚ_[p])=(u p:ℚ_[p])*s^2 := by
    simpa only [Int.cast_natCast] using he
  have hprod := (AuxiliaryLocalUnitClass318.prime_product_complement S α hS p hp).1
  have hid : σ*((∏ r∈S,r^α r):ℕ)*(q:ℤ)=((p:ℤ)^α p*E p)*(q:ℤ) := by
    rw [hprod]
    dsimp only [E]
    push_cast
    ring
  have hidQ := congrArg (fun z : ℤ => (z:ℚ_[p])) hid
  push_cast at hidQ
  refine ⟨s,hs,?_⟩
  calc
    _=((p:ℚ_[p])^α p*(E p:ℚ_[p]))*(q:ℚ_[p]) := by
      simpa only [Int.cast_mul,Int.cast_natCast,Int.cast_pow,Int.cast_prod,Nat.cast_prod,Nat.cast_pow] using hidQ
    _=(p:ℚ_[p])^α p*((E p:ℚ_[p])*(q:ℚ_[p])) := by ring
    _=_ := by rw [heQ]; ring

end AuxiliaryFiniteSquareclasses318
