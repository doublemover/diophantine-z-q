module
public import OriginalCommonGoodCutoff318
public section
noncomputable section
namespace OriginalGoodLatticeSieveUnion318
open scoped BigOperators
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open TriangularLatticeBoxCount318 OriginalAnisotropicRectangle318 OriginalSieveFrame318
open OriginalNormPointSieveTail318 OriginalCommonGoodCutoff318 OriginalThreeDimensionalTransference318
open OriginalThirdMinimumTail318
set_option maxHeartbeats 5000000

@[expose] def GoodParameters (κ label : ℤ) (T : ℝ) :=
  {s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
    Option (ZMod (LiteralSliceModulus318.prime κ label i)) //
    ¬LargeThird (LiteralSliceModulus318.prime κ label) κ s T}

@[expose] def GoodBoxFiber (B : ℕ) (side : Bool) (κ label : ℤ) (R T : ℝ) (Y : ℕ)
    (s : GoodParameters κ label T) :=
  {b : Box B // coordinates b∈literalLattice (LiteralSliceModulus318.prime κ label) κ s.1 ∧
    ‖embed (coordinates b)‖≤R ∧
    ∃ p : ↥(smallPrimes κ label Y (floorRadius (4*R/T))),
      pointObstruction side κ label (coordinates b) p.1}

/-- Original-coordinate good-lattice union, with no arbitrary basis
choice in its definition and a common prime interval across the family. -/
@[expose] def GoodSievePoints (B : ℕ) (side : Bool) (κ label : ℤ) (R T : ℝ) (Y : ℕ) :=
  {b : Box B // ∃ s : GoodParameters κ label T,
    coordinates b∈literalLattice (LiteralSliceModulus318.prime κ label) κ s.1 ∧
    ‖embed (coordinates b)‖≤R ∧
    ∃ p : ↥(smallPrimes κ label Y (floorRadius (4*R/T))),
      pointObstruction side κ label (coordinates b) p.1}

lemma good_box_fiber_tail (B : ℕ) (side : Bool) (κ label : ℤ) (R T : ℝ)
    (hR : 0≤R) (Y : ℕ) (hY : 0<Y) (s : GoodParameters κ label T) :
    (Nat.card (GoodBoxFiber B side κ label R T Y s):ℝ)*
      (LiteralSliceModulus318.modulus κ label:ℝ)^2*(Y:ℝ)≤110592*R^3 := by
  classical
  letI := normPoints_finite (κ := κ) (s := s.1)
    (LiteralSliceModulus318.prime_is_prime κ label) R hR
  let X := {y : NormPoints (LiteralSliceModulus318.prime κ label) κ s.1 R //
    ∃ p : ↥(smallPrimes κ label Y (floorRadius (4*R/T))),
      pointObstruction side κ label y.1.1 p.1}
  let f : GoodBoxFiber B side κ label R T Y s → X := fun b =>
    ⟨⟨⟨coordinates b.1,b.2.1⟩,b.2.2.1⟩,b.2.2.2⟩
  have hf : Function.Injective f := by
    intro a b he
    have hh := congrArg (fun y : X => y.1.1.1) he
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hh)
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun v : Vector ℤ => v.2.1) hh)
      · exact Subtype.ext (congrArg (fun v : Vector ℤ => v.2.2) hh)
  have hc : (Nat.card (GoodBoxFiber B side κ label R T Y s):ℝ)≤(Nat.card X:ℝ) := by
    exact_mod_cast Nat.card_le_card_of_injective f hf
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg _))
    (Nat.cast_nonneg Y)).trans (actual_common_good_tail side κ label s.1 T R hR Y hY s.2)

/-- All actual good lattices are now summed, with overlaps handled by a
witness injection. The exact finite family cardinality remains explicit;
there is no assumption that lattice pieces are disjoint. -/
theorem actual_good_family_tail (B : ℕ) (side : Bool) (κ label : ℤ) (R T : ℝ)
    (hR : 0≤R) (Y : ℕ) (hY : 0<Y) :
    (Nat.card (GoodSievePoints B side κ label R T Y):ℝ)*
      (LiteralSliceModulus318.modulus κ label:ℝ)^2*(Y:ℝ)≤
      (Nat.card (GoodParameters κ label T):ℝ)*(110592*R^3) := by
  classical
  letI : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      NeZero (LiteralSliceModulus318.prime κ label i) :=
    fun i => ⟨(LiteralSliceModulus318.prime_is_prime κ label i).ne_zero⟩
  let f : GoodSievePoints B side κ label R T Y →
      Σ s : GoodParameters κ label T, GoodBoxFiber B side κ label R T Y s :=
    fun b => ⟨b.2.choose,⟨b.1,b.2.choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun z : Σ s : GoodParameters κ label T,
      GoodBoxFiber B side κ label R T Y s => z.2.1) he)
  have hc : (Nat.card (GoodSievePoints B side κ label R T Y):ℝ)≤
      ∑ s : GoodParameters κ label T, (Nat.card (GoodBoxFiber B side κ label R T Y s):ℝ) := by
    have hh := Nat.card_le_card_of_injective f hf
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma] at hh
    exact_mod_cast hh
  calc
    _ ≤ (∑ s : GoodParameters κ label T, (Nat.card (GoodBoxFiber B side κ label R T Y s):ℝ))*
        (LiteralSliceModulus318.modulus κ label:ℝ)^2*(Y:ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) (Nat.cast_nonneg Y)
    _ = ∑ s : GoodParameters κ label T, (Nat.card (GoodBoxFiber B side κ label R T Y s):ℝ)*
        (LiteralSliceModulus318.modulus κ label:ℝ)^2*(Y:ℝ) := by rw [Finset.sum_mul,Finset.sum_mul]
    _ ≤ ∑ _s : GoodParameters κ label T, 110592*R^3 :=
      Finset.sum_le_sum (fun s _ => good_box_fiber_tail B side κ label R T hR Y hY s)
    _ = _ := by simp [Nat.card_eq_fintype_card]

end OriginalGoodLatticeSieveUnion318
