module
public import OriginalDualDenominator318
public section
noncomputable section
namespace OriginalEuclideanDualCount318
open scoped BigOperators RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 LiteralIntegerDuality318
open OriginalEuclideanLattice318 OriginalDualDenominator318 OriginalShortDualLattices318
open NonzeroMultipleBox318 TriangularLatticeBoxCount318
set_option maxHeartbeats 2500000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual STANDARD Euclidean dual radius, with denominator the
original modulus. No norm is transported from an abstract lattice. -/
@[expose] def EuclideanShort (p : ι → ℕ) (κ : ℤ) (B : ℕ) :=
  {t : ∀ i, Option (ZMod (p i)) // ∃ w : E, w∈Dual p κ t ∧ w≠0 ∧
    ‖w‖≤(B:ℝ)/(FixedSquarefreeCRT318.modulus p:ℝ)}

lemma normalized_norm_bound (M B : ℕ) (hM : 0<M) (v : Vector ℤ)
    (hv : ‖normalized M v‖≤(B:ℝ)/(M:ℝ)) : ‖embed v‖≤(B:ℝ) := by
  have hm : (0:ℝ)<M := by exact_mod_cast hM
  have he : (M:ℝ) • normalized M v=embed v := by
    simp only [normalized,smul_smul,mul_inv_cancel₀ hm.ne',one_smul]
  rw [←he,norm_smul,Real.norm_of_nonneg hm.le]
  calc
    (M:ℝ)*‖normalized M v‖≤(M:ℝ)*((B:ℝ)/(M:ℝ)) := mul_le_mul_of_nonneg_left hv hm.le
    _ = (B:ℝ) := by field_simp

/-- The Euclidean coordinate bound supplies actual membership in each
original integer interval, not a box in lattice-basis coordinates. -/
lemma integer_coordinates_bounded (B : ℕ) (v : Vector ℤ) (hv : ‖embed v‖≤(B:ℝ)) :
    |v.1|≤(B:ℤ) ∧ |v.2.1|≤(B:ℤ) ∧ |v.2.2|≤(B:ℤ) := by
  have h (i : Fin 3) : |embed v i|≤(B:ℝ) := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (embed v) i).trans hv
  have hx : |(v.1:ℝ)|≤(B:ℝ) := h 0
  have hz : |(v.2.1:ℝ)|≤(B:ℝ) := h 1
  have hw : |(v.2.2:ℝ)|≤(B:ℝ) := h 2
  exact ⟨by exact_mod_cast hx,by exact_mod_cast hz,by exact_mod_cast hw⟩

/-- Every genuine short Euclidean-dual vector gives the exact previously
counted NONZERO original integer annihilator, via its proved denominator. -/
theorem euclidean_short_to_integer (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (B : ℕ) (t : ∀ i, Option (ZMod (p i)))
    (ht : ∃ w : E, w∈Dual p κ t ∧ w≠0 ∧
      ‖w‖≤(B:ℝ)/(FixedSquarefreeCRT318.modulus p:ℝ)) :
    ∃ v : NonzeroBox B, ∀ u : Vector ℤ, u∈literalLattice p κ t →
      (FixedSquarefreeCRT318.modulus p:ℤ)∣dot (coordinates v.1) u := by
  obtain ⟨w,hw,hne,hbound⟩ := ht
  obtain ⟨v,hv,he⟩ := (actual_dual_iff p hp κ t w).mp hw
  have hvne : v≠0 := by
    intro hz
    apply hne
    rw [←he,hz,normalized_zero]
  have hn : ‖embed v‖≤(B:ℝ) := normalized_norm_bound _ B
    (FixedSquarefreeCRT318.modulus_positive p hp) v (by rwa [he])
  obtain ⟨hx,hz,hw'⟩ := integer_coordinates_bounded B v hn
  let vb : Box B := (⟨v.1,Finset.mem_Icc.mpr (abs_le.mp hx)⟩,
    ⟨v.2.1,Finset.mem_Icc.mpr (abs_le.mp hz)⟩,
    ⟨v.2.2,Finset.mem_Icc.mpr (abs_le.mp hw')⟩)
  refine ⟨⟨vb,?_⟩,?_⟩
  · change v≠0
    exact hvne
  · change ∀ u : Vector ℤ, u∈literalLattice p κ t →
      (FixedSquarefreeCRT318.modulus p:ℤ)∣dot v u
    exact hv

/-- The actual Euclidean-short-dual exceptional family has the same
quantitative bound. The still separate transference step must PRODUCE
such a vector from a large third minimum; this theorem does not assume
or assert that missing implication. -/
theorem actual_euclidean_short_count (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ) (B : ℕ) :
    Nat.card (EuclideanShort p κ B)≤27*4^(Fintype.card ι)*B^3 := by
  classical
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  let f : EuclideanShort p κ B → ShortDual p κ B := fun t =>
    ⟨t.1,euclidean_short_to_integer p hp κ B t.1 t.2⟩
  have hi : Function.Injective f := by
    intro s t he
    exact Subtype.ext (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective f hi).trans
    (original_short_dual_bound p hp hd κ hκ B)

end OriginalEuclideanDualCount318
