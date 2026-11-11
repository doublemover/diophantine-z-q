module
public import ActualQuarticSignedGoodTail318
public section
noncomputable section
namespace ActualGaussianGoodSlice318
open scoped BigOperators RealInnerProductSpace
open QuadricCRTAssembly318 LiteralQuarticSlice318 LiteralAdjacentNormSlice318
open LiteralSliceBoxCount318 LiteralSliceModulus318 TriangularLatticeBoxCount318
open OriginalGoodLatticeSieveUnion318 OriginalEuclideanLattice318
open ActualQuarticGoodFamily318 ActualGaussianChartObstruction318
open OriginalBadSliceLogWeight318
set_option maxHeartbeats 10000000

/-- Actual five-coordinate SECOND-chart source, with the literal adjacent
Gaussian norms. The same good-lattice witness is used by the bad-tail
decomposition; no abstract ternary obstruction replaces G or H here. -/
@[expose] def GoodSlice (B : ℕ) (κ t : ℤ) (T : ℝ) (Y : ℕ) :=
  {v : BoundedSlice B κ t true //
    (∃ s : GoodParameters κ t T,
      project v.1.1.1∈LiteralTernaryReduction318.literalLattice (prime κ t) κ s.1) ∧
    ∃ p : ℕ, p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣t ∧
      (p:ℤ)∣G v.1.1.1 ∧ (p:ℤ)∣H v.1.1.1}

/-- Euclidean radius is produced from the actual source box. We use the
safe uniform6B bound; this is not an extra norm hypothesis on the source. -/
lemma projected_norm (B : ℕ) (κ t : ℤ) (v : BoundedSlice B κ t true) :
    ‖embed (project v.1.1.1)‖≤6*(B:ℝ) := by
  let b := projectedBox B κ t true v
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
    GoodSlice B κ t T Y → GoodPoints (2*B) κ t (6*(B:ℝ)) T Y := by
  intro v
  refine ⟨projectedBox B κ t true v.1,?_⟩
  obtain ⟨s,hs⟩ := v.2.1
  refine ⟨s,hs,projected_norm B κ t v.1,?_⟩
  obtain ⟨p,hp,hYp,hκ,ht,hG,hH⟩ := v.2.2
  letI : Fact p.Prime := ⟨hp⟩
  have hp2 : p≠2 := by omega
  exact ⟨p,hp,hYp,hκ,ht,
    (original_source_iff p hp2 κ t ht true v.1.1).mp ⟨hG,hH⟩⟩

lemma sourceEncode_injective (B : ℕ) (κ t : ℤ) (ht : t≠0)
    (T : ℝ) (Y : ℕ) (hY : 3≤Y) : Function.Injective (sourceEncode B κ t T Y hY) := by
  intro v w he
  apply Subtype.ext
  apply LiteralSliceBoxCount318.encode_injective B κ t ht true
  apply Subtype.ext
  exact congrArg Subtype.val he

/-- The original point is kept exactly. Only an injective upper bound
discards parity; neither a unimodular source transform nor a bijection is claimed. -/
theorem actual_source_card (B : ℕ) (κ t : ℤ) (ht : t≠0)
    (T : ℝ) (Y : ℕ) (hY : 3≤Y) :
    Nat.card (GoodSlice B κ t T Y)≤Nat.card (GoodPoints (2*B) κ t (6*(B:ℝ)) T Y) :=
  Nat.card_le_card_of_injective (sourceEncode B κ t T Y hY)
    (sourceEncode_injective B κ t ht T Y hY)

end ActualGaussianGoodSlice318
