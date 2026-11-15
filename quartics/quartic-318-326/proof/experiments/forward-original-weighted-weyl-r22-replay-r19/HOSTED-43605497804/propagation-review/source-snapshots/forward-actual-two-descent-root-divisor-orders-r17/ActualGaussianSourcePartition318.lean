module
public import ActualFirstGaussianGoodSlice318
public section
noncomputable section
namespace ActualGaussianSourcePartition318
open scoped BigOperators
open LiteralQuarticSlice318 LiteralAdjacentNormSlice318 LiteralSliceBoxCount318 LiteralSliceModulus318
open LiteralTernaryReduction318 OriginalGoodLatticeSieveUnion318 OriginalBadSlicePointTail318
open OriginalWeightedSelberg318 OriginalBadSliceLogWeight318
set_option maxHeartbeats 11000000

/-- Actual original Gaussian obstruction on either nonzero-label chart.
No good-lattice choice is part of this source predicate. -/
@[expose] def SourceSlice (B : ℕ) (κ t : ℤ) (side : Bool) (Y : ℕ) :=
  {v : BoundedSlice B κ t side //
    ∃ p : ℕ, p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣t ∧
      (p:ℤ)∣G v.1.1.1 ∧ (p:ℤ)∣H v.1.1.1}

@[expose] def GoodChart (B : ℕ) (κ t : ℤ) (side : Bool) (T : ℝ) (Y : ℕ) :=
  {v : BoundedSlice B κ t side //
    (∃ s : GoodParameters κ t T, project v.1.1.1∈literalLattice (prime κ t) κ s.1) ∧
    ∃ p : ℕ, p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣t ∧
      (p:ℤ)∣G v.1.1.1 ∧ (p:ℤ)∣H v.1.1.1}

@[expose] def Target (B : ℕ) (κ t : ℤ) (side : Bool) (T : ℝ) (Y : ℕ) :=
  GoodChart B κ t side T Y ⊕ BadSlice B κ t side T
@[expose] def forget (B : ℕ) (κ t : ℤ) (side : Bool) (T : ℝ) (Y : ℕ) :
    Target B κ t side T Y → BoundedSlice B κ t side := Sum.elim Subtype.val Subtype.val

/-- Every original source point has an actual original lattice witness,
constructed from q(t)|R. Splitting THAT lattice at the unchanged LargeThird
predicate covers the source, even if other witness lattices overlap. -/
lemma source_cover (B : ℕ) (κ t : ℤ) (side : Bool) (T : ℝ) (Y : ℕ)
    (v : SourceSlice B κ t side Y) :
    ∃ u : Target B κ t side T Y, forget B κ t side T Y u=v.1 := by
  have hdiv := slice_modulus_divides κ t side v.1.1 (modulus κ t) (modulus_divides_label κ t)
  obtain ⟨s,hs⟩ := (literal_kernel_cover (prime κ t) (prime_is_prime κ t)
    (prime_injective κ t) (prime_odd κ t) κ (prime_avoids_coefficient κ t)
    (project v.1.1.1.1)).mp hdiv
  by_cases hbad : OriginalThreeDimensionalTransference318.LargeThird (prime κ t) κ s T
  · exact ⟨Sum.inr ⟨v.1,s,hbad,hs⟩,rfl⟩
  · exact ⟨Sum.inl ⟨v.1,⟨⟨⟨s,hbad⟩,hs⟩,v.2⟩⟩,rfl⟩

@[expose] def sourceChoice (B : ℕ) (κ t : ℤ) (side : Bool) (T : ℝ) (Y : ℕ) :
    SourceSlice B κ t side Y → Target B κ t side T Y :=
  fun v => (source_cover B κ t side T Y v).choose
lemma sourceChoice_forget (B : ℕ) (κ t : ℤ) (side : Bool) (T : ℝ) (Y : ℕ)
    (v : SourceSlice B κ t side Y) :
    forget B κ t side T Y (sourceChoice B κ t side T Y v)=v.1 :=
  (source_cover B κ t side T Y v).choose_spec
lemma sourceChoice_injective (B : ℕ) (κ t : ℤ) (side : Bool) (T : ℝ) (Y : ℕ) :
    Function.Injective (sourceChoice B κ t side T Y) := by
  intro v w he
  apply Subtype.ext
  have hh := congrArg (forget B κ t side T Y) he
  simpa only [sourceChoice_forget] using hh

variable {J : Type*} [Fintype J] [DecidableEq J]
@[expose] def goodMass (B : ℕ) (κ t : ℤ) (side : Bool) (T : ℝ) (Y : ℕ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (GoodChart B κ t side T Y) := Fintype.ofFinite _
  exact ∑ v : GoodChart B κ t side T Y, weight κ γ v.1.1.1
@[expose] def sourceMass (B : ℕ) (κ t : ℤ) (side : Bool) (Y : ℕ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (SourceSlice B κ t side Y) := Fintype.ofFinite _
  exact ∑ v : SourceSlice B κ t side Y, weight κ γ v.1.1.1

/-- Actual weighted source cover. The injection preserves the original
five-coordinate point and therefore its exact original logarithmic weight.
Bad points need not satisfy the obstruction for this upper bound. -/
theorem original_weighted_partition (B : ℕ) (κ t : ℤ) (side : Bool)
    (T : ℝ) (Y : ℕ) (γ : J → ℤ) :
    sourceMass B κ t side Y γ≤goodMass B κ t side T Y γ+
      logarithmicMass B κ t side T γ := by
  classical
  letI : Fintype (SourceSlice B κ t side Y) := Fintype.ofFinite _
  letI : Fintype (GoodChart B κ t side T Y) := Fintype.ofFinite _
  letI : Fintype (BadSlice B κ t side T) := Fintype.ofFinite _
  let wt : Target B κ t side T Y → ℝ :=
    fun v => weight κ γ (forget B κ t side T Y v).1.1
  have hh := hasSum_le_inj (sourceChoice B κ t side T Y)
    (sourceChoice_injective B κ t side T Y)
    (fun v _ => weight_nonneg κ γ (forget B κ t side T Y v).1.1)
    (fun v => le_of_eq (by dsimp [wt];rw [sourceChoice_forget]))
    (hasSum_fintype (fun v : SourceSlice B κ t side Y => weight κ γ v.1.1.1))
    (hasSum_fintype wt)
  simpa only [sourceMass,goodMass,logarithmicMass,Target,Fintype.sum_sum_type,
    wt,forget,Sum.elim_inl,Sum.elim_inr] using hh

end ActualGaussianSourcePartition318
