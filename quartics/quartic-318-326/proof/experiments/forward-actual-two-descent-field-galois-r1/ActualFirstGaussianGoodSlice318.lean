module
public import ActualFirstChartLabelTail318
public section
noncomputable section
namespace ActualFirstGaussianGoodSlice318
open scoped BigOperators RealInnerProductSpace
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralAdjacentNormSlice318
open LiteralSliceBoxCount318 LiteralSliceModulus318 TriangularLatticeBoxCount318
open OriginalGoodLatticeSieveUnion318 OriginalEuclideanLattice318
open OriginalGoodAllPrimeFamily318 ActualGaussianChartObstruction318
open OriginalBadSliceLogWeight318
set_option maxHeartbeats 10000000

/-- Actual five-coordinate FIRST-chart source, with the literal adjacent
Gaussian norms. The same good-lattice witness is used by the bad-tail
decomposition; no abstract ternary obstruction replaces G or H here. -/
@[expose] def GoodSlice (B : ℕ) (κ t : ℤ) (T : ℝ) (Y : ℕ) :=
  {v : BoundedSlice B κ t false //
    (∃ s : GoodParameters κ t T,
      project v.1.1.1∈LiteralTernaryReduction318.literalLattice (prime κ t) κ s.1) ∧
    ∃ p : ℕ, p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣t ∧
      (p:ℤ)∣G v.1.1.1 ∧ (p:ℤ)∣H v.1.1.1}

/-- Euclidean radius is produced from the actual source box. We use the
safe uniform6B bound; this is not an extra norm hypothesis on the source. -/
lemma projected_norm (B : ℕ) (κ t : ℤ) (v : BoundedSlice B κ t false) :
    ‖embed (project v.1.1.1)‖≤6*(B:ℝ) := by
  let b := projectedBox B κ t false v
  have hx := square_bound (2*B) b.1.1 (Finset.mem_Icc.mp b.1.2)
  have hz := square_bound (2*B) b.2.1.1 (Finset.mem_Icc.mp b.2.1.2)
  have hw := square_bound (2*B) b.2.2.1 (Finset.mem_Icc.mp b.2.2.2)
  have hxr : (b.1.1:ℝ)^2≤(2*(B:ℝ))^2 := by exact_mod_cast hx
  have hzr : (b.2.1.1:ℝ)^2≤(2*(B:ℝ))^2 := by exact_mod_cast hz
  have hwr : (b.2.2.1:ℝ)^2≤(2*(B:ℝ))^2 := by exact_mod_cast hw
  have hn : ‖embed (coordinates b)‖^2=
      (b.1.1:ℝ)^2+(b.2.1.1:ℝ)^2+(b.2.2.1:ℝ)^2 := by
    rw [←real_inner_self_eq_norm_sq,inner_embed]
    simp only [LiteralIntegerDuality318.dot,coordinates]
    push_cast
    ring
  change ‖embed (coordinates b)‖≤6*(B:ℝ)
  nlinarith [norm_nonneg (embed (coordinates b)),Nat.cast_nonneg B]

@[expose] def sourceEncode (B : ℕ) (κ t : ℤ) (T : ℝ) (Y : ℕ) (hY : 3≤Y) :
    GoodSlice B κ t T Y → GoodPoints (2*B) false κ t (6*(B:ℝ)) T Y := by
  intro v
  refine ⟨projectedBox B κ t false v.1,?_⟩
  obtain ⟨s,hs⟩ := v.2.1
  refine ⟨s,hs,projected_norm B κ t v.1,?_⟩
  obtain ⟨p,hp,hYp,hκ,ht,hG,hH⟩ := v.2.2
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p≠2 := by omega
  exact ⟨p,hp,hYp,hκ,ht,
    (first_abstract_iff κ t (project v.1.1.1.1) p).mp
      ((original_source_iff p hp2 κ t ht false v.1.1).mp ⟨hG,hH⟩)⟩

lemma sourceEncode_injective (B : ℕ) (κ t : ℤ) (ht : t≠0)
    (T : ℝ) (Y : ℕ) (hY : 3≤Y) : Function.Injective (sourceEncode B κ t T Y hY) := by
  intro v w he
  apply Subtype.ext
  apply LiteralSliceBoxCount318.encode_injective B κ t ht false
  apply Subtype.ext
  exact congrArg Subtype.val he

/-- The original point is kept exactly. Only an injective upper bound
discards parity; neither a unimodular source transform nor a bijection is claimed. -/
theorem actual_source_card (B : ℕ) (κ t : ℤ) (ht : t≠0)
    (T : ℝ) (Y : ℕ) (hY : 3≤Y) :
    Nat.card (GoodSlice B κ t T Y)≤Nat.card (GoodPoints (2*B) false κ t (6*(B:ℝ)) T Y) :=
  Nat.card_le_card_of_injective (sourceEncode B κ t T Y hY)
    (sourceEncode_injective B κ t ht T Y hY)



open ActualFirstChartLabelTail318 OriginalUniformEulerRankin318 OriginalGlobalBadMass318
open OriginalWeightedSelberg318
variable {J : Type*} [Fintype J] [DecidableEq J]

@[expose] def mass (B : ℕ) (κ t : ℤ) (T : ℝ) (Y : ℕ) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (GoodSlice B κ t T Y) := Fintype.ofFinite _
  exact ∑ v : GoodSlice B κ t T Y, weight κ γ v.1.1.1

lemma mass_le_card (B : ℕ) (hB : 1≤B) (κ t : ℤ) (T : ℝ) (Y : ℕ) (γ : J → ℤ) :
    mass B κ t T Y γ≤(Nat.card (GoodSlice B κ t T Y):ℝ)*weightCeiling B γ := by
  classical
  letI : Fintype (GoodSlice B κ t T Y) := Fintype.ofFinite _
  calc
    _ ≤ ∑ _v : GoodSlice B κ t T Y, weightCeiling B γ :=
      Finset.sum_le_sum (fun v _ => original_weight_bound B hB κ t false γ v.1)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]

@[expose] def totalMass (B : ℕ) (κ : ℤ) (T : ℝ) (Y : ℕ) (γ : J → ℤ) : ℝ :=
  ∑ t∈labels B, mass B κ t T Y γ

/-- The literal original logarithmic weights and all signed source labels
are now consumed, not supplied as a bound. This is the actual FIRST-chart
good-lattice contribution; zero labels, bad lattices, primes dividing the
label, and the other chart remain separate parts of the final sieve. -/
theorem actual_original_weighted_good_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0)
    (T : ℝ) (hT : 0≤T) (hTB : T≤6*(B:ℝ)) (Y : ℕ) (hY : 3≤Y)
    (γ : J → ℤ) (δ : ℝ) (hδ : 0<δ) :
    totalMass B κ T Y γ*Real.log (Y:ℝ)≤
      (2*rankinConstant κ δ*(2*(B:ℝ))^δ)*
        labelBudget κ B (6*(B:ℝ)) T Y*weightCeiling B γ := by
  have hW := weightCeiling_nonneg B hB γ
  have hlog := Real.log_nonneg (show (1:ℝ)≤Y by exact_mod_cast (show 1≤Y by omega))
  have hfixed (t : ℤ) (ht : t∈labels B) :
      mass B κ t T Y γ≤
        (Nat.card (OriginalGoodAllPrimeFamily318.GoodPoints (2*B) false κ t (6*(B:ℝ)) T Y):ℝ)*weightCeiling B γ := by
    have hc : (Nat.card (GoodSlice B κ t T Y):ℝ)≤
        (Nat.card (OriginalGoodAllPrimeFamily318.GoodPoints (2*B) false κ t (6*(B:ℝ)) T Y):ℝ) := by
      exact_mod_cast actual_source_card B κ t (label_ne_zero B t ht) T Y hY
    exact (mass_le_card B hB κ t T Y γ).trans (mul_le_mul_of_nonneg_right hc hW)
  have hs := Finset.sum_le_sum hfixed
  have hm : totalMass B κ T Y γ≤signedCount (2*B) B κ (6*(B:ℝ)) T Y*weightCeiling B γ := by
    simpa only [totalMass,signedCount,Finset.sum_mul] using hs
  have hc := actual_signed_good_tail (2*B) B κ hκ (6*(B:ℝ)) T
    (by positivity) hT hTB Y hY δ hδ
  calc
    _ ≤ (signedCount (2*B) B κ (6*(B:ℝ)) T Y*weightCeiling B γ)*Real.log (Y:ℝ) :=
      mul_le_mul_of_nonneg_right hm hlog
    _ = (signedCount (2*B) B κ (6*(B:ℝ)) T Y*Real.log (Y:ℝ))*weightCeiling B γ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hW


end ActualFirstGaussianGoodSlice318
