module
public import ActualOriginalLevelSource318
public section
noncomputable section
namespace ActualSquareDivisibleValues318
open scoped BigOperators
open IntegerResidueBoxCount318
set_option maxHeartbeats 11000000

/-- Nonzero integer levels in the ORIGINAL bounded interval, divisible by
the actual positive modulus d. Zero is explicitly excluded. -/
@[expose] def Values (N d : ℕ) := {v : Interval N // v.1≠0 ∧ (d:ℤ)∣v.1}

lemma magnitude_bound (N d : ℕ) (v : Values N d) : v.1.1.natAbs≤N := by
  have hh : |v.1.1|≤(N:ℤ) := abs_le.mpr (Finset.mem_Icc.mp v.1.2)
  have hz : (v.1.1.natAbs:ℤ)≤N := by simpa only [Int.natCast_natAbs] using hh
  exact_mod_cast hz
lemma divides_magnitude (N d : ℕ) (v : Values N d) : d∣v.1.1.natAbs := by
  have hh := Int.natAbs_dvd_natAbs.mpr v.2.2
  simpa only [Int.natAbs_natCast] using hh

/-- Sign and the actual positive quotient recover every nonzero level.
This gives the full1/d saving, with no additive1 from the zero level. -/
@[expose] def encode (N d : ℕ) (hd : 0<d) (v : Values N d) :
    Bool×↥(Finset.Icc 1 (N/d)) :=
  (decide (v.1.1<0),⟨v.1.1.natAbs/d,Finset.mem_Icc.mpr ⟨by
    have he := Nat.div_mul_cancel (divides_magnitude N d v)
    have hn := Int.natAbs_pos.mpr v.2.1
    by_contra hh
    have hz : v.1.1.natAbs/d=0 := by omega
    rw [hz,zero_mul] at he
    omega,
    Nat.div_le_div_right (magnitude_bound N d v)⟩⟩)

lemma encode_injective (N d : ℕ) (hd : 0<d) : Function.Injective (encode N d hd) := by
  intro v w he
  have hs : decide (v.1.1<0)=decide (w.1.1<0) := congrArg Prod.fst he
  have hq : v.1.1.natAbs/d=w.1.1.natAbs/d :=
    congrArg (fun z : Bool×↥(Finset.Icc 1 (N/d)) => z.2.1) he
  have hn : v.1.1.natAbs=w.1.1.natAbs := by
    have hh := congrArg (fun q : ℕ => q*d) hq
    simpa only [Nat.div_mul_cancel (divides_magnitude N d v),
      Nat.div_mul_cancel (divides_magnitude N d w)] using hh
  have ha : |v.1.1|=|w.1.1| := by
    simpa only [Int.natCast_natAbs] using congrArg (fun n : ℕ => (n:ℤ)) hn
  apply Subtype.ext
  apply Subtype.ext
  by_cases hv : v.1.1<0
  · have hw : w.1.1<0 := by by_contra hh;simp [hv,hh] at hs
    exact neg_injective (by simpa only [abs_of_neg hv,abs_of_neg hw] using ha)
  · have hw : ¬w.1.1<0 := by intro hh;simp [hv,hh] at hs
    simpa only [abs_of_nonneg (le_of_not_gt hv),abs_of_nonneg (le_of_not_gt hw)] using ha

theorem actual_nonzero_multiple_count (N d : ℕ) (hd : 0<d) :
    Nat.card (Values N d)≤2*(N/d) := by
  have hh := Nat.card_le_card_of_injective (encode N d hd) (encode_injective N d hd)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_bool,
    Fintype.card_coe,Nat.card_Icc,Nat.add_sub_cancel] using hh

theorem actual_scaled_multiple_count (N d : ℕ) (hd : 0<d) :
    Nat.card (Values N d)*d≤2*N := by
  have hh := Nat.mul_le_mul_right d (actual_nonzero_multiple_count N d hd)
  have hdiv := Nat.div_mul_le_self N d
  nlinarith

/-- The ORIGINAL R range is abs(R)<=4B². Every p²-divisible NONZERO
level is counted with weight p^-2, including negative values. -/
theorem actual_square_level_count (B p : ℕ) (hp : 0<p) :
    (Nat.card (Values (4*B^2) (p^2)):ℝ)≤8*(B:ℝ)^2/(p:ℝ)^2 := by
  have hh := actual_scaled_multiple_count (4*B^2) (p^2) (pow_pos hp 2)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  apply (le_div_iff₀ (sq_pos_of_pos hpR)).mpr
  exact_mod_cast hh

end ActualSquareDivisibleValues318
