module
public import ActualTZPrimeUniverseDigits318
public section
noncomputable section
namespace ActualTZBooleanPrimeSlots318
open scoped BigOperators
open ActualTZPrimeUniverseDigits318
attribute [local instance] Classical.propDecidable

abbrev Slot (I : Type*) := I × Bool
abbrev PrimeAt (P : ℕ) := ↥(Nat.primesBelow P)
abbrev Choices (I : Type*) (P : ℕ) := PrimeAt P→((I→Bool)×(I→Bool))

variable {I : Type*}

@[expose] def bit (P : ℕ) (x : Choices I P) (p : PrimeAt P) (j : Slot I) : Bool :=
  if j.2 then (x p).1 j.1 else (x p).2 j.1

def mask (P : ℕ) (x : Choices I P) (j : Slot I) : Subsets P :=
  ⟨(Nat.primesBelow P).filter (fun p => ∃ hp : p∈Nat.primesBelow P,
      bit P x ⟨p,hp⟩ j=true),Finset.filter_subset _ _⟩

theorem mem_mask (P : ℕ) (x : Choices I P) (p : PrimeAt P) (j : Slot I) :
    p.val∈(mask P x j).val ↔ bit P x p j=true := by
  unfold mask
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_,h,h'⟩
    exact h'
  · intro H
    exact ⟨p.property,p.property,H⟩

def fromMasks (P : ℕ) (x : Slot I→Subsets P) : Choices I P :=
  fun p => (fun i => decide (p.val∈(x (i,true)).val),
            fun i => decide (p.val∈(x (i,false)).val))

/-- Swaps finite indexing of the actual existing row slots without
dropping or identifying any slot; Bool.true is the first old divisor. -/
def maskEquiv (P : ℕ) : Choices I P ≃ (Slot I→Subsets P) where
  toFun x := mask P x
  invFun x := fromMasks P x
  left_inv x := by
    funext p
    apply Prod.ext
    · funext i
      change decide (p.val∈(mask P x (i,true)).val)=(x p).1 i
      have H := mem_mask P x p (i,true)
      cases h : (x p).1 i <;> simp_all [bit]
    · funext i
      change decide (p.val∈(mask P x (i,false)).val)=(x p).2 i
      have H := mem_mask P x p (i,false)
      cases h : (x p).2 i <;> simp_all [bit]
  right_inv x := by
    funext j
    apply Subtype.ext
    ext p
    by_cases hp : p∈Nat.primesBelow P
    · change (⟨p,hp⟩ : PrimeAt P).val∈(mask P (fromMasks P x) j).val ↔ _
      rw [mem_mask]
      rcases j with ⟨i,b⟩
      cases b <;> simp [bit,fromMasks]
    · constructor
      · intro h
        exact (hp ((mask P (fromMasks P x) j).property h)).elim
      · intro h
        exact (hp ((x j).property h)).elim

def toDigits (P : ℕ) : Choices I P ≃ (Slot I→Supported P) :=
  (maskEquiv P).trans (Equiv.piCongrRight (fun _ => equiv P))

@[expose] def digit (P : ℕ) (x : Choices I P) (j : Slot I) : ℕ :=
  (toDigits P x j).val

theorem digit_prod (P : ℕ) (x : Choices I P) (j : Slot I) :
    digit P x j=∏ p∈(mask P x j).val,p := by
  change (equiv P (mask P x j)).val=_
  exact equiv_apply_val P _

theorem digit_squarefree (P : ℕ) (x : Choices I P) (j : Slot I) :
    Squarefree (digit P x j) := (toDigits P x j).property.1

theorem digit_supported (P : ℕ) (x : Choices I P) (j : Slot I) :
    (digit P x j).primeFactors⊆Nat.primesBelow P := (toDigits P x j).property.2

theorem digit_support_eq (P : ℕ) (x : Choices I P) (j : Slot I) :
    (digit P x j).primeFactors=(mask P x j).val := by
  rw [digit_prod,Nat.primeFactors_prod]
  exact fun _ hp => Nat.prime_of_mem_primesBelow ((mask P x j).property hp)

theorem digit_iff_bit (P : ℕ) (x : Choices I P) (p : PrimeAt P) (j : Slot I) :
    p.val∣digit P x j ↔ bit P x p j=true := by
  have hp := Nat.prime_of_mem_primesBelow p.property
  have hd := (digit_squarefree P x j).ne_zero
  have H : p.val∣digit P x j ↔ p.val∈(digit P x j).primeFactors :=
    ⟨fun h => Nat.mem_primeFactors.2 ⟨hp,h,hd⟩,fun h => (Nat.mem_primeFactors.1 h).2.1⟩
  rw [H,digit_support_eq,mem_mask]

end ActualTZBooleanPrimeSlots318
