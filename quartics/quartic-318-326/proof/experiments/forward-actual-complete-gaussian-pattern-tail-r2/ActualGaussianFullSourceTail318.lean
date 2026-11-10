module
public import ActualBothLabelPrimeTail318
public section
noncomputable section
namespace ActualGaussianFullSourceTail318
open scoped BigOperators
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralAdjacentNormSlice318 LiteralSliceBoxCount318
open LiteralTernaryReduction318 OriginalGlobalBadSource318 OriginalGlobalBadMass318
open ActualGaussianSourcePartition318 ActualGaussianTwoChartTail318 ActualGaussianPowerSaving318
open OriginalBadSliceLogWeight318 OriginalWeightedSelberg318
set_option maxHeartbeats 16000000

/-- Entire actual original G/H large-common-prime source in the box.
Only the fixed exceptional primes dividing kappa remain excluded; they
are handled by putting Y above that finite fixed set, not by a label shift. -/
@[expose] def FullSource (B : ℕ) (κ : ℤ) (Y : ℕ) :=
  {v : Quadric κ // InBox B v.1 ∧
    ∃ p : ℕ, p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ (p:ℤ)∣G v.1 ∧ (p:ℤ)∣H v.1}
@[expose] def ChartSource (B : ℕ) (κ : ℤ) (Y : ℕ) :=
  Σ side : Bool, Σ t : ↥(labels B), SourceSlice B κ t.1 side Y
@[expose] def Target (B : ℕ) (κ : ℤ) (Y : ℕ) :=
  ActualGaussianZeroStratum318.ZeroSource B κ ⊕
    (ActualBothLabelPrimeTail318.BothSource B κ Y ⊕ ChartSource B κ Y)
@[expose] def forget (B : ℕ) (κ : ℤ) (Y : ℕ) : Target B κ Y → Quadric κ :=
  Sum.elim Subtype.val (Sum.elim Subtype.val (fun v => v.2.2.1.1.1))

/-- Complete original-source cover. Zero R, nonzero R with both labels
divisible, and a genuine nonzero-label chart exhaust EVERY original point.
The selected chart uses the SAME prime and original G/H values. -/
lemma source_cover (B : ℕ) (κ : ℤ) (Y : ℕ) (v : FullSource B κ Y) :
    ∃ z : Target B κ Y, forget B κ Y z=v.1 := by
  by_cases hz : R κ (project v.1.1)=0
  · exact ⟨Sum.inl ⟨v.1,v.2.1,hz⟩,rfl⟩
  obtain ⟨p,hp,hYp,hκ,hG,hH⟩ := v.2.2
  by_cases h0 : (p:ℤ)∣x0 v.1.1
  · by_cases h1 : (p:ℤ)∣x1 v.1.1
    · exact ⟨Sum.inr (Sum.inl ⟨v.1,v.2.1,hz,p,hp,hYp,h0,h1⟩),rfl⟩
    · have ht : x1 v.1.1≠0 := by intro h;apply h1;rw [h];exact dvd_zero _
      have hm := actual_label_mem B false v.1.1 v.2.1 ht
      exact ⟨Sum.inr (Sum.inr ⟨false,⟨x1 v.1.1,hm⟩,
        ⟨⟨⟨v.1,rfl⟩,v.2.1⟩,p,hp,hYp,hκ,h1,hG,hH⟩⟩),rfl⟩
  · have ht : x0 v.1.1≠0 := by intro h;apply h0;rw [h];exact dvd_zero _
    have hm := actual_label_mem B true v.1.1 v.2.1 ht
    exact ⟨Sum.inr (Sum.inr ⟨true,⟨x0 v.1.1,hm⟩,
      ⟨⟨⟨v.1,rfl⟩,v.2.1⟩,p,hp,hYp,hκ,h0,hG,hH⟩⟩),rfl⟩

@[expose] def sourceChoice (B : ℕ) (κ : ℤ) (Y : ℕ) :
    FullSource B κ Y → Target B κ Y := fun v => (source_cover B κ Y v).choose
lemma sourceChoice_forget (B : ℕ) (κ : ℤ) (Y : ℕ) (v : FullSource B κ Y) :
    forget B κ Y (sourceChoice B κ Y v)=v.1 := (source_cover B κ Y v).choose_spec
lemma sourceChoice_injective (B : ℕ) (κ : ℤ) (Y : ℕ) :
    Function.Injective (sourceChoice B κ Y) := by
  intro v w he
  apply Subtype.ext
  have hh := congrArg (forget B κ Y) he
  simpa only [sourceChoice_forget] using hh
instance fullSource_finite (B : ℕ) (κ : ℤ) (Y : ℕ) : Finite (FullSource B κ Y) :=
  Finite.of_injective (sourceChoice B κ Y) (sourceChoice_injective B κ Y)

variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def mass (B : ℕ) (κ : ℤ) (Y : ℕ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (FullSource B κ Y) := Fintype.ofFinite _
  exact ∑ v : FullSource B κ Y,weight κ γ v.1

lemma original_full_partition (B : ℕ) (κ : ℤ) (Y : ℕ) (γ : J → ℤ) :
    mass B κ Y γ≤ActualGaussianZeroStratum318.mass B κ γ+
      ActualBothLabelPrimeTail318.mass B κ Y γ+twoChartMass B κ Y γ := by
  classical
  letI : Fintype (FullSource B κ Y) := Fintype.ofFinite _
  letI : Fintype (ActualGaussianZeroStratum318.ZeroSource B κ) := Fintype.ofFinite _
  letI : Fintype (ActualBothLabelPrimeTail318.BothSource B κ Y) := Fintype.ofFinite _
  letI : ∀ side : Bool, ∀ t : ↥(labels B), Fintype (SourceSlice B κ t.1 side Y) :=
    fun _ _ => Fintype.ofFinite _
  let wt : Target B κ Y → ℝ := fun v => weight κ γ (forget B κ Y v)
  have hh := hasSum_le_inj (sourceChoice B κ Y) (sourceChoice_injective B κ Y)
    (fun v _ => weight_nonneg κ γ (forget B κ Y v))
    (fun v => le_of_eq (by dsimp [wt];rw [sourceChoice_forget]))
    (hasSum_fintype (fun v : FullSource B κ Y => weight κ γ v.1)) (hasSum_fintype wt)
  have he : (∑ v : Target B κ Y,wt v)=ActualGaussianZeroStratum318.mass B κ γ+
      ActualBothLabelPrimeTail318.mass B κ Y γ+twoChartMass B κ Y γ := by
    simp only [Target,Fintype.sum_sum_type,ChartSource,Fintype.sum_sigma,Fintype.sum_bool,
      wt,forget,Sum.elim_inl,Sum.elim_inr,ActualGaussianZeroStratum318.mass,
      ActualBothLabelPrimeTail318.mass,twoChartMass,ActualGaussianTwoChartTail318.sourceTotal,
      ActualGaussianSourcePartition318.sourceMass,Finset.sum_coe_sort]
    ring
  exact hh.trans_eq he

/-- Full actual original logarithmic large-common-prime upper bound,
including zero-label/R=0 and both-label-divisible strata. The remaining
mathematical task is prime production, not an unconstructed source cover.
This is an upper bound and does not assert existence of prime patterns. -/
theorem actual_full_gaussian_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (Y : ℕ) (hY : 3≤Y) (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    mass B κ Y γ≤weightCeiling B γ*
      (ActualGaussianZeroStratum318.zeroBudget B κ δ+
        (8*(B:ℝ)^2/(Y:ℝ))*ActualOriginalLevelSource318.valueBudget B κ δ+
        optimizedBudget κ δ B Y) := by
  have hp := original_full_partition B κ Y γ
  have hz := ActualGaussianZeroStratum318.actual_weighted_zero_source_tail B hB κ hκ δ hδ γ
  have hb := ActualBothLabelPrimeTail318.actual_weighted_both_label_tail B hB κ hκ Y
    (by omega) δ hδ γ
  have hc := actual_original_power_saving B hB κ hκ Y hY γ δ hδ
  nlinarith only [hp,hz,hb,hc]


/-- No excluded-prime predicate in this source. The cutoff above the
FIXED original coefficient support is constructed in the equivalence. -/
@[expose] def AllPrimeSource (B : ℕ) (κ : ℤ) (Y : ℕ) :=
  {v : Quadric κ // InBox B v.1 ∧
    ∃ p : ℕ, p.Prime ∧ Y<p ∧ (p:ℤ)∣G v.1 ∧ (p:ℤ)∣H v.1}

@[expose] def allPrimeEquiv (B : ℕ) (κ : ℤ) (hκ : κ≠0) (Y : ℕ)
    (hκY : κ.natAbs≤Y) : AllPrimeSource B κ Y ≃ FullSource B κ Y where
  toFun v := ⟨v.1,v.2.1,by
    obtain ⟨p,hp,hYp,hG,hH⟩ := v.2.2
    refine ⟨p,hp,hYp,?_,hG,hH⟩
    intro hd
    have hn : p∣κ.natAbs := by
      simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hκ) hn
    omega⟩
  invFun v := ⟨v.1,v.2.1,by
    obtain ⟨p,hp,hYp,_,hG,hH⟩ := v.2.2
    exact ⟨p,hp,hYp,hG,hH⟩⟩
  left_inv v := rfl
  right_inv v := rfl

/-- All large primes are covered once Y is above the actual fixed
coefficient support. The counted source has no label, R, lattice, parity,
or coefficient-prime restrictions beyond the original quadric and box. -/
theorem actual_all_prime_gaussian_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (Y : ℕ) (hY : 3≤Y) (hκY : κ.natAbs≤Y) (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    letI : Fintype (FullSource B κ Y) := Fintype.ofFinite _
    letI : Fintype (AllPrimeSource B κ Y) := Fintype.ofEquiv (FullSource B κ Y)
      (allPrimeEquiv B κ hκ Y hκY).symm
    (∑ v : AllPrimeSource B κ Y,weight κ γ v.1)≤weightCeiling B γ*
      (ActualGaussianZeroStratum318.zeroBudget B κ δ+
        (8*(B:ℝ)^2/(Y:ℝ))*ActualOriginalLevelSource318.valueBudget B κ δ+
        optimizedBudget κ δ B Y) := by
  classical
  letI : Fintype (FullSource B κ Y) := Fintype.ofFinite _
  letI : Fintype (AllPrimeSource B κ Y) := Fintype.ofEquiv (FullSource B κ Y)
    (allPrimeEquiv B κ hκ Y hκY).symm
  have he : (∑ v : AllPrimeSource B κ Y,weight κ γ v.1)=mass B κ Y γ := by
    exact Equiv.sum_comp (allPrimeEquiv B κ hκ Y hκY) (fun v => weight κ γ v.1)
  rw [he]
  exact actual_full_gaussian_tail B hB κ hκ Y hY γ δ hδ

end ActualGaussianFullSourceTail318
