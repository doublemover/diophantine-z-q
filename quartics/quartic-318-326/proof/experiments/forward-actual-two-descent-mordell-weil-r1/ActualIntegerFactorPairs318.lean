module
public import ActualGaussianPowerSaving318
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public section
noncomputable section
namespace ActualIntegerFactorPairs318
open IntegerResidueBoxCount318
set_option maxHeartbeats 11000000

@[expose] def Pairs (B : ℕ) (n : ℤ) :=
  {v : Interval B×Interval B // v.1.1*v.2.1=n}
lemma left_ne_zero (B : ℕ) (n : ℤ) (hn : n≠0) (v : Pairs B n) : v.1.1.1≠0 := by
  intro he
  have hh := v.2
  rw [he,zero_mul] at hh
  exact hn hh.symm

/-- Signed factor pairs are injected into the ACTUAL positive divisors
and one sign. This counts all original integer factorizations, not just
primitive pairs, squarefree divisors, or residue classes. -/
@[expose] def encode (B : ℕ) (n : ℤ) (hn : n≠0) (v : Pairs B n) :
    Bool×↥(n.natAbs.divisors) :=
  (decide (v.1.1.1<0),⟨v.1.1.1.natAbs,Nat.mem_divisors.mpr ⟨
    Int.natAbs_dvd_natAbs.mpr ⟨v.1.2.1,v.2.symm⟩,Int.natAbs_ne_zero.mpr hn⟩⟩)

lemma encode_injective (B : ℕ) (n : ℤ) (hn : n≠0) : Function.Injective (encode B n hn) := by
  intro v w he
  have hs : decide (v.1.1.1<0)=decide (w.1.1.1<0) := congrArg Prod.fst he
  have ha : |v.1.1.1|=|w.1.1.1| := by
    have hh := congrArg (fun z : Bool×↥(n.natAbs.divisors) => z.2.1) he
    simpa only [Int.natCast_natAbs] using congrArg (fun a : ℕ => (a:ℤ)) hh
  have hx : v.1.1.1=w.1.1.1 := by
    by_cases hv : v.1.1.1<0
    · have hw : w.1.1.1<0 := by by_contra hh;simp [hv,hh] at hs
      exact neg_injective (by simpa only [abs_of_neg hv,abs_of_neg hw] using ha)
    · have hw : ¬w.1.1.1<0 := by intro hh;simp [hv,hh] at hs
      simpa only [abs_of_nonneg (le_of_not_gt hv),abs_of_nonneg (le_of_not_gt hw)] using ha
  have hy : v.1.2.1=w.1.2.1 := by
    apply mul_left_cancel₀ (left_ne_zero B n hn v)
    rw [v.2,hx,w.2]
  exact Subtype.ext (Prod.ext (Subtype.ext hx) (Subtype.ext hy))

theorem actual_factor_count (B : ℕ) (n : ℤ) (hn : n≠0) :
    Nat.card (Pairs B n)≤2*n.natAbs.divisors.card := by
  have hh := Nat.card_le_card_of_injective (encode B n hn) (encode_injective B n hn)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe] using hh

/-- Zero products are a DIFFERENT stratum: both coordinate axes are kept.
This bound deliberately permits the origin to be counted twice. -/
theorem zero_factor_count (B : ℕ) : Nat.card (Pairs B 0)≤2*(2*B+1) := by
  classical
  let f : Pairs B 0 → Bool×Interval B := fun v =>
    if h : v.1.1.1=0 then (false,v.1.2) else (true,v.1.1)
  have hf : Function.Injective f := by
    intro v w he
    have hv := mul_eq_zero.mp v.2
    have hw := mul_eq_zero.mp w.2
    by_cases hx : v.1.1.1=0 <;> by_cases hy : w.1.1.1=0
    · have hh : v.1.2=w.1.2 := congrArg Prod.snd (by simpa only [f,dif_pos hx,dif_pos hy] using he)
      exact Subtype.ext (Prod.ext (Subtype.ext (hx.trans hy.symm)) hh)
    · have hh := congrArg Prod.fst he
      simp [f,hx,hy] at hh
    · have hh := congrArg Prod.fst he
      simp [f,hx,hy] at hh
    · have hh : v.1.1=w.1.1 := congrArg Prod.snd (by simpa only [f,dif_neg hx,dif_neg hy] using he)
      exact Subtype.ext (Prod.ext hh (Subtype.ext ((hv.resolve_left hx).trans (hw.resolve_left hy).symm)))
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_bool,
    Interval,Fintype.card_coe,interval_card] using hh

end ActualIntegerFactorPairs318
