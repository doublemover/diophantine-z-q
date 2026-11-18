module
public import FixedSelectedPrimeBound318
public import Mathlib.Algebra.GCDMonoid.Finset
public section
noncomputable section
namespace ActualSelectedOrderModuli318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318 ConcretePadic318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hp : Values C u w)

/-- The two embeddings at every original position are specified by ONE
actual root. The later rational-ray producer supplies its existence. -/
@[expose] def Roots : Type := ∀ i : Fin 3 × Fin 5,
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
  {rho : ℚ_[p] // rho^2=2}

@[expose] def primaryOrder (r : Roots C u w hp) (i : Fin 3 × Fin 5) : ℕ :=
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
  SelectedQuotientOrders318.order p (r i).val (r i).property

@[expose] def oppositeOrder (r : Roots C u w hp) (i : Fin 3 × Fin 5) : ℕ :=
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp i.1 i.2⟩
  SelectedQuotientOrders318.order p (-(r i).val) (negative_root p (r i).val (r i).property)

@[expose] def minus (r : Roots C u w hp) : ℕ := Finset.univ.lcm (primaryOrder C u w hp r)
@[expose] def plus (r : Roots C u w hp) : ℕ := Finset.univ.lcm (oppositeOrder C u w hp r)

lemma primary_positive (r : Roots C u w hp) (i : Fin 3 × Fin 5) :
    0<primaryOrder C u w hp r i := by
  dsimp [primaryOrder]
  exact SelectedQuotientOrders318.order_positive _ _ _

lemma opposite_positive (r : Roots C u w hp) (i : Fin 3 × Fin 5) :
    0<oppositeOrder C u w hp r i := by
  dsimp [oppositeOrder]
  exact SelectedQuotientOrders318.order_positive _ _ _

lemma positive (r : Roots C u w hp) : 0<minus C u w hp r ∧ 0<plus C u w hp r := by
  constructor
  · apply Nat.pos_of_ne_zero
    exact Finset.lcm_ne_zero_iff.mpr (fun i _ => Nat.ne_of_gt (primary_positive C u w hp r i))
  · apply Nat.pos_of_ne_zero
    exact Finset.lcm_ne_zero_iff.mpr (fun i _ => Nat.ne_of_gt (opposite_positive C u w hp r i))

lemma primary_dvd (r : Roots C u w hp) (i : Fin 3 × Fin 5) :
    primaryOrder C u w hp r i∣minus C u w hp r := Finset.dvd_lcm (Finset.mem_univ i)
lemma opposite_dvd (r : Roots C u w hp) (i : Fin 3 × Fin 5) :
    oppositeOrder C u w hp r i∣plus C u w hp r := Finset.dvd_lcm (Finset.mem_univ i)

/-- The exact two moduli are constructed from the actual finite formal
quotients. Repeated prime positions remain attached to their actual root;
the least common multiple handles repetitions without losing an entry. -/
theorem orders (r : Roots C u w hp) :
    SelectedTraceFromOrders318.Orders C u w hp (minus C u w hp r) (plus C u w hp r) := by
  intro j i
  dsimp only
  exact ⟨(r (j,i)).val,(r (j,i)).property,primary_dvd C u w hp r (j,i),
    opposite_dvd C u w hp r (j,i)⟩

/-- An eventual CM/order comparison only needs to prove that each ACTUAL
quotient order divides the proposed arithmetic order. This theorem is a
consumer, not a claim that that geometric comparison has been proved. -/
theorem divides_proposed (r : Roots C u w hp) (Mminus Mplus : ℕ)
    (hm : ∀ i, primaryOrder C u w hp r i∣Mminus)
    (hp' : ∀ i, oppositeOrder C u w hp r i∣Mplus) :
    minus C u w hp r∣Mminus ∧ plus C u w hp r∣Mplus :=
  ⟨Finset.lcm_dvd (fun i _ => hm i),Finset.lcm_dvd (fun i _ => hp' i)⟩

end ActualSelectedOrderModuli318
