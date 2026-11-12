module
public import ActualOriginalMinorRationalIntegral318
public import ActualIntegerFactorPairs318
public section
noncomputable section
namespace ActualOriginalSquareDifferenceFibers318
open IntegerResidueBoxCount318 ActualIntegerFactorPairs318

@[expose] def SquarePairs (H : ℕ) (n : ℤ) :=
  {p : Interval H×Interval H // p.1.1^2-p.2.1^2=n}

/-- Difference of squares is injected into all SIGNED factor pairs.
The parity restriction is enlarged, never incorrectly imposed as an equivalence. -/
@[expose] def factorMap (H : ℕ) (n : ℤ) (p : SquarePairs H n) : Pairs (2*H) n := by
  have hx := Finset.mem_Icc.mp p.1.1.2
  have hy := Finset.mem_Icc.mp p.1.2.2
  refine ⟨(⟨p.1.1.1-p.1.2.1,?_⟩,⟨p.1.1.1+p.1.2.1,?_⟩),?_⟩
  · apply Finset.mem_Icc.mpr
    push_cast
    constructor <;> omega
  · apply Finset.mem_Icc.mpr
    push_cast
    constructor <;> omega
  · have hh := p.2
    nlinarith only [hh]

lemma actual_factorMap_injective (H : ℕ) (n : ℤ) : Function.Injective (factorMap H n) := by
  intro p q he
  have hs := congrArg (fun z : Pairs (2*H) n => z.1.1.1) he
  have ht := congrArg (fun z : Pairs (2*H) n => z.1.2.1) he
  change p.1.1.1-p.1.2.1=q.1.1.1-q.1.2.1 at hs
  change p.1.1.1+p.1.2.1=q.1.1.1+q.1.2.1 at ht
  exact Subtype.ext (Prod.ext (Subtype.ext (by omega)) (Subtype.ext (by omega)))

lemma actual_nonzero_square_pair_count (H : ℕ) (n : ℤ) (hn : n≠0) :
    Nat.card (SquarePairs H n)≤2*n.natAbs.divisors.card :=
  (Nat.card_le_card_of_injective (factorMap H n) (actual_factorMap_injective H n)).trans
    (actual_factor_count (2*H) n hn)

/-- The zero fiber has the two genuine diagonal lines x=y and x=-y.
It is counted separately, not passed to a nonzero divisor estimate. -/
lemma actual_zero_square_pair_count (H : ℕ) : Nat.card (SquarePairs H 0)≤2*(2*H+1) := by
  classical
  let f : SquarePairs H 0 → Bool×Interval H := fun p => (decide (p.1.1.1=p.1.2.1),p.1.2)
  have root (p : SquarePairs H 0) : p.1.1.1=p.1.2.1 ∨ p.1.1.1= -p.1.2.1 := by
    have hh : (p.1.1.1-p.1.2.1)*(p.1.1.1+p.1.2.1)=0 := by nlinarith only [p.2]
    rcases mul_eq_zero.mp hh with h|h
    · exact Or.inl (sub_eq_zero.mp h)
    · right;linarith
  have hf : Function.Injective f := by
    intro p q he
    have hy : p.1.2=q.1.2 := congrArg Prod.snd he
    have hs := congrArg Prod.fst he
    have hx : p.1.1.1=q.1.1.1 := by
      by_cases hp : p.1.1.1=p.1.2.1
      · have hq : q.1.1.1=q.1.2.1 := by by_contra hh;simp [f,hp,hh] at hs
        exact hp.trans ((congrArg Subtype.val hy).trans hq.symm)
      · have hq : q.1.1.1≠q.1.2.1 := by intro hh;simp [f,hp,hh] at hs
        rw [(root p).resolve_left hp,(root q).resolve_left hq,hy]
    exact Subtype.ext (Prod.ext (Subtype.ext hx) hy)
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_bool,
    Interval,Fintype.card_coe,OriginalOffsetZeroLocus318.interval_card] using hh

end ActualOriginalSquareDifferenceFibers318
