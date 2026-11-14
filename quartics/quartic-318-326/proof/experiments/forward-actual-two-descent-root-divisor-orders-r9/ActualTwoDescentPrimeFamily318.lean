module
public import ActualTwoDescentSupportConditions318
public import ActualTwoDescentReciprocalPrime318
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Data.Fin.Tuple.Basic
public section
noncomputable section
namespace ActualTwoDescentPrimeFamily318
open ActualTwoDescentResidueBits318 ActualTwoDescentPrescribedPrime318
set_option maxHeartbeats 16000000

/-- Actual finite auxiliary primes, with the complete triangular table of
symbols against every previously chosen prime. Jacobi notation keeps the
record independent of choices of proof instances; each denominator is prime. -/
structure PrimeFamily {ι : Type*} (p : ι → ℕ)
    (oldBits : ℕ → ι → Bool) (newBits : ℕ → ℕ → Bool)
    (special : ℕ → Bool) (forbidden : Finset ℕ) (N k : ℕ) where
  value : Fin k → ℕ
  prime : ∀ i, (value i).Prime
  large : ∀ i, max N 2 < value i
  injective : Function.Injective value
  seed_ne : ∀ i j, value i ≠ p j
  avoid : ∀ i, value i ∉ forbidden
  residue : ∀ i, (value i : ZMod 12)=(if special i.val then 7 else 1)
  coprime : ∀ i, Nat.Coprime (value i) 12
  old_symbol : ∀ i j, jacobiSym (value i : ℤ) (p j)=bitSign (oldBits i.val j)
  earlier_symbol : ∀ i j, j.val < i.val →
    jacobiSym (value i : ℤ) (value j)=bitSign (newBits i.val j.val)

/-- One more prime is chosen only after all earlier primes, but realizes
all old and earlier symbol requirements simultaneously. The same prefix
values are retained, not merely replaced by another equinumerous family. -/
theorem actual_append {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hcop : ∀ i, Nat.Coprime (p i) 12) (hp2 : ∀ i, p i ≠ 2)
    (oldBits : ℕ → ι → Bool) (newBits : ℕ → ℕ → Bool)
    (special : ℕ → Bool) (forbidden : Finset ℕ) (N k : ℕ)
    (F : PrimeFamily p oldBits newBits special forbidden N k) :
    ∃ G : PrimeFamily p oldBits newBits special forbidden N (k+1),
      ∀ i, G.value i.castSucc=F.value i := by
  classical
  let r : ι ⊕ Fin k → ℕ := Sum.elim p F.value
  let bits : ι ⊕ Fin k → Bool := Sum.elim (oldBits k) (fun j => newBits k j.val)
  letI : ∀ i, Fact (r i).Prime := fun i => ⟨by
    cases i with
    | inl i => exact Fact.out
    | inr j => exact F.prime j⟩
  have hr : Function.Injective r := by
    intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (hd he)
      | inr j => exact False.elim (F.seed_ne j i he.symm)
    | inr i =>
      cases j with
      | inl j => exact False.elim (F.seed_ne i j he)
      | inr j => exact congrArg Sum.inr (F.injective he)
  have hrc : ∀ i, Nat.Coprime (r i) 12 := by
    intro i
    cases i with
    | inl i => exact hcop i
    | inr j => exact F.coprime j
  have hr2 : ∀ i, r i ≠ 2 := by
    intro i
    cases i with
    | inl i => exact hp2 i
    | inr j => exact ne_of_gt (lt_of_le_of_lt (le_max_right _ _) (F.large j))
  obtain ⟨q,hq,hprime,havoid,hfresh,htype,hbits⟩ :=
    actual_prescribed_prime r hr hrc hr2 bits (special k) forbidden (max N 2)
  have hqc : Nat.Coprime q 12 := by
    apply (ZMod.isUnit_iff_coprime q 12).mp
    rw [htype]
    cases hs : special k
    · exact isUnit_one
    · exact (ZMod.unitOfCoprime 7 (by decide)).isUnit
  have hsym : ∀ i, jacobiSym (q : ℤ) (r i)=bitSign (bits i) := by
    intro i
    rw [←legendreSym.to_jacobiSym]
    simpa only [legendreSym, Int.cast_natCast] using hbits i
  let G : PrimeFamily p oldBits newBits special forbidden N (k+1) :=
    { value := Fin.snoc F.value q
      prime := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using hprime
        · simpa only [Fin.snoc_castSucc] using F.prime j
      large := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using hq
        · simpa only [Fin.snoc_castSucc] using F.large j
      injective := Fin.snoc_injective_of_injective F.injective (by
        rintro ⟨j,hj⟩
        exact hfresh (Sum.inr j) hj.symm)
      seed_ne := by
        intro i j
        refine Fin.lastCases ?_ (fun l => ?_) i
        · simpa only [Fin.snoc_last] using hfresh (Sum.inl j)
        · simpa only [Fin.snoc_castSucc] using F.seed_ne l j
      avoid := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using havoid
        · simpa only [Fin.snoc_castSucc] using F.avoid j
      residue := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last, Fin.val_last] using htype
        · simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using F.residue j
      coprime := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using hqc
        · simpa only [Fin.snoc_castSucc] using F.coprime j
      old_symbol := by
        intro i j
        refine Fin.lastCases ?_ (fun l => ?_) i
        · simpa only [Fin.snoc_last, Fin.val_last, r, bits, Sum.elim_inl] using hsym (Sum.inl j)
        · simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using F.old_symbol l j
      earlier_symbol := by
        intro i j
        refine Fin.lastCases ?_ (fun l => ?_) i
        · refine Fin.lastCases ?_ (fun t => ?_) j
          · intro h
            exact False.elim (Nat.lt_irrefl _ h)
          · intro _
            simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last, Fin.val_castSucc,
              r, bits, Sum.elim_inr] using hsym (Sum.inr t)
        · refine Fin.lastCases ?_ (fun t => ?_) j
          · intro h
            exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt l.isLt) h)
          · intro h
            simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using F.earlier_symbol l t h }
  refine ⟨G,?_⟩
  intro i
  exact Fin.snoc_castSucc _ _ _

/-- Every finite triangular prescription has an actual prime realization.
There is no supplied sequence of suitable primes or residue units. -/
theorem actual_finite_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) [∀ i, Fact (p i).Prime] (hd : Function.Injective p)
    (hcop : ∀ i, Nat.Coprime (p i) 12) (hp2 : ∀ i, p i ≠ 2)
    (oldBits : ℕ → ι → Bool) (newBits : ℕ → ℕ → Bool)
    (special : ℕ → Bool) (forbidden : Finset ℕ) (N k : ℕ) :
    Nonempty (PrimeFamily p oldBits newBits special forbidden N k) := by
  induction k with
  | zero =>
    exact ⟨{ value := Fin.elim0
             prime := Fin.elim0
             large := Fin.elim0
             injective := fun i => Fin.elim0 i
             seed_ne := Fin.elim0
             avoid := Fin.elim0
             residue := Fin.elim0
             coprime := Fin.elim0
             old_symbol := Fin.elim0
             earlier_symbol := Fin.elim0 }⟩
  | succ k ih =>
    obtain ⟨F⟩ := ih
    obtain ⟨G,_⟩ := actual_append p hd hcop hp2 oldBits newBits special forbidden N k F
    exact ⟨G⟩

end ActualTwoDescentPrimeFamily318
