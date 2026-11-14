module
public import ActualSquareDivisibleValues318
public section
noncomputable section
namespace ActualBothLabelPrimeTail318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralSliceBoxCount318 LiteralTernaryReduction318
open ActualOriginalLevelSource318 ActualSquareDivisibleValues318
open OriginalReciprocalSquareTail318 OriginalBadSliceLogWeight318 OriginalWeightedSelberg318
set_option maxHeartbeats 15000000

/-- The full NONZERO-R original source with a large prime dividing BOTH
original labels. Gaussian G/H conditions are safely discarded only here. -/
@[expose] def BothSource (B : ℕ) (κ : ℤ) (Y : ℕ) :=
  {v : Quadric κ // InBox B v.1 ∧ R κ (project v.1)≠0 ∧
    ∃ p : ℕ, p.Prime ∧ Y<p ∧ (p:ℤ)∣x0 v.1 ∧ (p:ℤ)∣x1 v.1}
@[expose] def primes (B Y : ℕ) : Finset ℕ :=
  (Finset.range (2*B+1)).filter (fun p => p.Prime ∧ Y<p)
@[expose] def Target (B : ℕ) (κ : ℤ) (Y : ℕ) :=
  Σ p : ↥(primes B Y), Σ z : Values (4*B^2) (p.1^2), ValueSource B κ z.1.1

lemma prime_bound (B : ℕ) (κ : ℤ) (v : BothSource B κ 0)
    (p : ℕ) (hp : p.Prime) (h0 : (p:ℤ)∣x0 v.1.1) : p≤2*B := by
  have hx : x0 v.1.1≠0 := by
    intro hz
    have hh := factorization κ v.1
    rw [hz,zero_mul] at hh
    exact v.2.2.1 hh.symm
  have hd : p∣(x0 v.1.1).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr h0
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hx) hd
  have hb : (x0 v.1.1).natAbs≤2*B := by
    obtain ⟨ha,_,hc,_,_⟩ := v.2.1
    have hh : |x0 v.1.1|≤(2*B:ℤ) := by
      apply abs_le.mpr
      dsimp [x0]
      constructor <;> omega
    have hn : ((x0 v.1.1).natAbs:ℤ)≤(2*B:ℤ) := by simpa only [Int.natCast_natAbs] using hh
    exact_mod_cast hn
  exact hle.trans hb

/-- Actual p²|R is derived from BOTH original labels, with p<=2B
derived from the original nonzero label. No infinite-prime union is used. -/
lemma source_cover (B : ℕ) (κ : ℤ) (Y : ℕ) (v : BothSource B κ Y) :
    ∃ z : Target B κ Y, z.2.2.1=v.1 := by
  obtain ⟨p,hp,hYp,h0,h1⟩ := v.2.2.2
  have hB := prime_bound B κ ⟨v.1,v.2.1,v.2.2.1,p,hp,hp.pos,h0,h1⟩ p hp h0
  have hm : p∈primes B Y := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega),hp,hYp⟩
  let r := R κ (project v.1.1)
  have hr : r≠0 := v.2.2.1
  have hdiv : ((p^2:ℕ):ℤ)∣r := by
    have hh := mul_dvd_mul h0 h1
    rw [factorization κ v.1] at hh
    simpa only [Nat.cast_pow,pow_two] using hh
  have habs : |r|≤4*(B:ℤ)^2 := actual_value_abs B κ r ⟨v.1,v.2.1,rfl⟩
  have hinterval : r∈Finset.Icc (-((4*B^2:ℕ):ℤ)) (4*B^2:ℕ) := by
    apply Finset.mem_Icc.mpr
    have hh := abs_le.mp habs
    exact_mod_cast hh
  exact ⟨⟨⟨p,hm⟩,⟨⟨r,hinterval⟩,hr,hdiv⟩,⟨v.1,v.2.1,rfl⟩⟩,rfl⟩

@[expose] def sourceChoice (B : ℕ) (κ : ℤ) (Y : ℕ) :
    BothSource B κ Y → Target B κ Y := fun v => (source_cover B κ Y v).choose
lemma sourceChoice_injective (B : ℕ) (κ : ℤ) (Y : ℕ) :
    Function.Injective (sourceChoice B κ Y) := by
  intro v u he
  apply Subtype.ext
  have hh := congrArg (fun z : Target B κ Y => z.2.2.1) he
  simpa only [sourceChoice,(source_cover B κ Y v).choose_spec,
    (source_cover B κ Y u).choose_spec] using hh
instance bothSource_finite (B : ℕ) (κ : ℤ) (Y : ℕ) : Finite (BothSource B κ Y) :=
  Finite.of_injective (sourceChoice B κ Y) (sourceChoice_injective B κ Y)

theorem actual_both_label_count (B : ℕ) (κ : ℤ) (hκ : κ≠0) (Y : ℕ) (hY : 0<Y)
    (δ : ℝ) (hδ : 0<δ) :
    (Nat.card (BothSource B κ Y):ℝ)≤(8*(B:ℝ)^2/(Y:ℝ))*valueBudget B κ δ := by
  classical
  letI : ∀ p : ↥(primes B Y), ∀ z : Values (4*B^2) (p.1^2),
      Fintype (ValueSource B κ z.1.1) := fun _ _ => Fintype.ofFinite _
  have hc : (Nat.card (BothSource B κ Y):ℝ)≤
      ∑ p : ↥(primes B Y), ∑ z : Values (4*B^2) (p.1^2),
        (Nat.card (ValueSource B κ z.1.1):ℝ) := by
    have hh := Nat.card_le_card_of_injective (sourceChoice B κ Y) (sourceChoice_injective B κ Y)
    simp only [Nat.card_eq_fintype_card,Target,Fintype.card_sigma] at hh
    exact_mod_cast hh
  have hV := valueBudget_nonneg B κ δ hδ
  have hp (p : ↥(primes B Y)) :
      (∑ z : Values (4*B^2) (p.1^2),(Nat.card (ValueSource B κ z.1.1):ℝ))≤
        (8*(B:ℝ)^2/(p.1:ℝ)^2)*valueBudget B κ δ := by
    have hprime := (Finset.mem_filter.mp p.2).2.1
    have hs := Finset.sum_le_sum (fun (z : Values (4*B^2) (p.1^2)) (_ : z∈Finset.univ) =>
      actual_value_source_count B κ z.1.1 hκ z.2.1 (by
        have hh := abs_le.mpr (Finset.mem_Icc.mp z.1.2)
        exact_mod_cast hh) δ hδ)
    have hcount := mul_le_mul_of_nonneg_right (actual_square_level_count B p.1 hprime.pos) hV
    have hs' : (∑ z : Values (4*B^2) (p.1^2),(Nat.card (ValueSource B κ z.1.1):ℝ))≤
        (Nat.card (Values (4*B^2) (p.1^2)):ℝ)*valueBudget B κ δ := by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card] using hs
    exact hs'.trans hcount
  have hs := hc.trans (Finset.sum_le_sum (fun p _ => hp p))
  have hr := finite_reciprocal_tail Y hY (primes B Y)
    (fun p hp => (Finset.mem_filter.mp hp).2.2)
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (by positivity : 0≤8*(B:ℝ)^2)) hV
  calc
    _ ≤ ∑ p : ↥(primes B Y),(8*(B:ℝ)^2/(p.1:ℝ)^2)*valueBudget B κ δ := hs
    _ = ((8*(B:ℝ)^2)*(∑ p∈primes B Y,1/(p:ℝ)^2))*valueBudget B κ δ := by
      rw [←Finset.sum_mul,Finset.sum_coe_sort,Finset.mul_sum]
      apply congrArg (fun a => a*valueBudget B κ δ)
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := by simpa only [div_eq_mul_inv,one_mul] using hm

variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def mass (B : ℕ) (κ : ℤ) (Y : ℕ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (BothSource B κ Y) := Fintype.ofFinite _
  exact ∑ v : BothSource B κ Y, weight κ γ v.1

theorem actual_weighted_both_label_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (Y : ℕ) (hY : 0<Y) (δ : ℝ) (hδ : 0<δ) (γ : J → ℤ) :
    mass B κ Y γ≤(8*(B:ℝ)^2/(Y:ℝ))*valueBudget B κ δ*weightCeiling B γ := by
  classical
  letI : Fintype (BothSource B κ Y) := Fintype.ofFinite _
  have hm : mass B κ Y γ≤(Nat.card (BothSource B κ Y):ℝ)*weightCeiling B γ := by
    calc
      _ ≤ ∑ _v : BothSource B κ Y,weightCeiling B γ :=
        Finset.sum_le_sum (fun v _ => original_weight_bound B hB κ (x0 v.1.1) true γ
          ⟨⟨v.1,rfl⟩,v.2.1⟩)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  exact hm.trans (mul_le_mul_of_nonneg_right (actual_both_label_count B κ hκ Y hY δ hδ)
    (weightCeiling_nonneg B hB γ))

end ActualBothLabelPrimeTail318
