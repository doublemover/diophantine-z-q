module
public import ActualQuarticNormAllPrime318
public section
noncomputable section
namespace ActualQuarticGoodFamily318
open scoped BigOperators
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open TriangularLatticeBoxCount318 OriginalAnisotropicRectangle318 OriginalSieveFrame318
open OriginalNormPointSieveTail318 OriginalGoodLatticeSieveUnion318 ActualQuarticNormAllPrime318
open ActualGaussianChartObstruction318
set_option maxHeartbeats 8500000

local instance goodFintype (κ t : ℤ) (T : ℝ) : Fintype (GoodParameters κ t T) := by
  classical
  letI : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
      NeZero (LiteralSliceModulus318.prime κ t k) :=
    fun k => ⟨(LiteralSliceModulus318.prime_is_prime κ t k).ne_zero⟩
  infer_instance

@[expose] def Obstructed (κ t : ℤ) (Y : ℕ) (y : Vector ℤ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ Y<p ∧ ¬(p:ℤ)∣κ ∧ ¬(p:ℤ)∣t ∧ Obstruction true κ t y p

@[expose] def GoodFiber (B : ℕ) (κ t : ℤ) (R T : ℝ) (Y : ℕ)
    (s : GoodParameters κ t T) :=
  {b : Box B // coordinates b∈literalLattice (LiteralSliceModulus318.prime κ t) κ s.1 ∧
    ‖embed (coordinates b)‖≤R ∧ Obstructed κ t Y (coordinates b)}

/-- Actual original-coordinate good-lattice union with ALL permitted
primes above Y. The good predicate is the unchanged old bad-tail complement. -/
@[expose] def GoodPoints (B : ℕ) (κ t : ℤ) (R T : ℝ) (Y : ℕ) :=
  {b : Box B // ∃ s : GoodParameters κ t T,
    coordinates b∈literalLattice (LiteralSliceModulus318.prime κ t) κ s.1 ∧
    ‖embed (coordinates b)‖≤R ∧ Obstructed κ t Y (coordinates b)}

lemma good_fiber_tail (B : ℕ) (κ t : ℤ) (hκ : κ≠0) (ht0 : t≠0) (R T : ℝ)
    (hR : 0≤R) (Y : ℕ) (hY : 3≤Y) (s : GoodParameters κ t T) :
    (Nat.card (GoodFiber B κ t R T Y s):ℝ)*Real.log (Y:ℝ)≤pointBudget κ t s.1 R Y := by
  classical
  letI := normPoints_finite (κ := κ) (s := s.1)
    (LiteralSliceModulus318.prime_is_prime κ t) R hR
  let f : GoodFiber B κ t R T Y s → NormBad κ t s.1 R Y := fun b =>
    ⟨⟨⟨coordinates b.1,b.2.1⟩,b.2.2.1⟩,b.2.2.2⟩
  have hf : Function.Injective f := by
    intro a b he
    have hh := congrArg (fun y : NormBad κ t s.1 R Y => y.1.1.1) he
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hh)
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun v : Vector ℤ => v.2.1) hh)
      · exact Subtype.ext (congrArg (fun v : Vector ℤ => v.2.2) hh)
  have hc : (Nat.card (GoodFiber B κ t R T Y s):ℝ)≤(Nat.card (NormBad κ t s.1 R Y):ℝ) := by
    exact_mod_cast Nat.card_le_card_of_injective f hf
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  exact (mul_le_mul_of_nonneg_right hc hl).trans (actual_norm_all_prime_tail κ t hκ ht0 s.1 R hR Y hY)

/-- Every actual good lattice is summed with overlap-safe witness
injection. The RHS is the explicit finite sum of CONSTRUCTED reciprocal
frame budgets; optimizing that sum is still a distinct arithmetic step. -/
theorem actual_good_all_prime_tail (B : ℕ) (κ t : ℤ) (hκ : κ≠0) (ht0 : t≠0) (R T : ℝ)
    (hR : 0≤R) (Y : ℕ) (hY : 3≤Y) :
    (Nat.card (GoodPoints B κ t R T Y):ℝ)*Real.log (Y:ℝ)≤
      ∑ s : GoodParameters κ t T, pointBudget κ t s.1 R Y := by
  classical
  let f : GoodPoints B κ t R T Y → Σ s : GoodParameters κ t T, GoodFiber B κ t R T Y s :=
    fun b => ⟨b.2.choose,⟨b.1,b.2.choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun z : Σ s : GoodParameters κ t T, GoodFiber B κ t R T Y s => z.2.1) he)
  have hc : (Nat.card (GoodPoints B κ t R T Y):ℝ)≤
      ∑ s : GoodParameters κ t T, (Nat.card (GoodFiber B κ t R T Y s):ℝ) := by
    have hh := Nat.card_le_card_of_injective f hf
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma] at hh
    exact_mod_cast hh
  have hl : 0≤Real.log (Y:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤Y by omega))
  calc
    _ ≤ (∑ s : GoodParameters κ t T, (Nat.card (GoodFiber B κ t R T Y s):ℝ))*Real.log (Y:ℝ) :=
      mul_le_mul_of_nonneg_right hc hl
    _ = ∑ s : GoodParameters κ t T, (Nat.card (GoodFiber B κ t R T Y s):ℝ)*Real.log (Y:ℝ) :=
      Finset.sum_mul
    _ ≤ _ := Finset.sum_le_sum (fun s _ => good_fiber_tail B κ t hκ ht0 R T hR Y hY s)

end ActualQuarticGoodFamily318
