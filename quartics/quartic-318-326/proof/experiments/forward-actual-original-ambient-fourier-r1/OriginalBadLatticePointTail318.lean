module
public import OriginalThirdMinimumTail318
public section
noncomputable section
namespace OriginalBadLatticePointTail318
open scoped BigOperators
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 TriangularLatticeBoxCount318
open OriginalThreeDimensionalTransference318 OriginalThirdMinimumTail318
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def LiteralLatticeBox (B : ℕ) (p : ι → ℕ) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) := {v : Box B // coordinates v∈literalLattice p κ t}

/-- Exact original per-lattice box count. The already proved literal
subgroup equality uses the general engine ONLY at2κ, on unchanged points. -/
theorem literal_lattice_box_scaled (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) (hB : FixedSquarefreeCRT318.modulus p≤B) :
    Nat.card (LiteralLatticeBox B p κ t)*(FixedSquarefreeCRT318.modulus p)^2≤27*B^3 := by
  have he : LiteralLatticeBox B p κ t ≃ OriginalTernaryBoxCount318.OriginalBox B p hp (2*κ) t := {
    toFun := fun v => ⟨v.1,by rw [←literal_lattice_eq p hp hp2 κ t]; exact v.2⟩
    invFun := fun v => ⟨v.1,by rw [literal_lattice_eq p hp hp2 κ t]; exact v.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr he]
  exact OriginalTernaryBoxCount318.original_lattice_scaled B p hp hd (2*κ) t hB

/-- Actual ORIGINAL coordinate points lying on at least one exceptional
lattice. Overlaps are not interpreted as disjoint pieces. -/
@[expose] def BadPoints (B : ℕ) (p : ι → ℕ) (κ : ℤ) (T : ℝ) :=
  {v : Box B // ∃ t : ∀ i, Option (ZMod (p i)), LargeThird p κ t T ∧ coordinates v∈literalLattice p κ t}

@[expose] def incidenceChoice (B : ℕ) (p : ι → ℕ) (κ : ℤ) (T : ℝ) :
    BadPoints B p κ T → Σ t : Exceptional p κ T, LiteralLatticeBox B p κ t.1 := fun v =>
  ⟨⟨v.2.choose,v.2.choose_spec.1⟩,⟨v.1,v.2.choose_spec.2⟩⟩

lemma incidenceChoice_injective (B : ℕ) (p : ι → ℕ) (κ : ℤ) (T : ℝ) :
    Function.Injective (incidenceChoice B p κ T) := by
  intro v w he
  apply Subtype.ext
  exact congrArg (fun z : Σ t : Exceptional p κ T, LiteralLatticeBox B p κ t.1 => z.2.1) he

/-- Point mass in the actual exceptional-family union, rather than only
a count of abstract lattice parameters. Actual residue fibers give the
uniform per-lattice factor, so no successive-minima basis/count is assumed. -/
theorem bad_points_scaled (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ) (T : ℝ)
    (hB : FixedSquarefreeCRT318.modulus p≤B) :
    Nat.card (BadPoints B p κ T)*(FixedSquarefreeCRT318.modulus p)^2≤
      Nat.card (Exceptional p κ T)*(27*B^3) := by
  classical
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  have hh := Nat.card_le_card_of_injective (incidenceChoice B p κ T)
    (incidenceChoice_injective B p κ T)
  have hc : Nat.card (BadPoints B p κ T)≤
      ∑ t : Exceptional p κ T, Nat.card (LiteralLatticeBox B p κ t.1) := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using hh
  calc
    _ ≤ (∑ t : Exceptional p κ T, Nat.card (LiteralLatticeBox B p κ t.1))*
        (FixedSquarefreeCRT318.modulus p)^2 := Nat.mul_le_mul_right _ hc
    _ = ∑ t : Exceptional p κ T, Nat.card (LiteralLatticeBox B p κ t.1)*
        (FixedSquarefreeCRT318.modulus p)^2 := Finset.sum_mul _ _ _
    _ ≤ ∑ _t : Exceptional p κ T, 27*B^3 :=
      Finset.sum_le_sum (fun t ht => literal_lattice_box_scaled B p hp hd hp2 κ t.1 hB)
    _ = Nat.card (Exceptional p κ T)*(27*B^3) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]

/-- Exact fixed-modulus ORIGINAL bad-point tail. The q² point-count
factor cancels against the actual lattice-family q³ tail, leaving q. -/
theorem actual_bad_point_tail (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ) (hκ : ∀ i, ¬(p i:ℤ)∣κ)
    (T : ℝ) (hT : 0<T) (hB : FixedSquarefreeCRT318.modulus p≤B) :
    (Nat.card (BadPoints B p κ T):ℝ)*T^3≤
      5832*(4:ℝ)^(Fintype.card ι)*(FixedSquarefreeCRT318.modulus p:ℝ)*(B:ℝ)^3 := by
  let M := FixedSquarefreeCRT318.modulus p
  have hM : (0:ℝ)<M := by exact_mod_cast FixedSquarefreeCRT318.modulus_positive p hp
  have hpnt : (Nat.card (BadPoints B p κ T):ℝ)*(M:ℝ)^2≤
      (Nat.card (Exceptional p κ T):ℝ)*(27*(B:ℝ)^3) := by
    exact_mod_cast bad_points_scaled B p hp hd hp2 κ T hB
  have hfamily := actual_third_minimum_tail p hp hd κ hκ T hT
  have hscaled : ((Nat.card (BadPoints B p κ T):ℝ)*T^3)*(M:ℝ)^2≤
      (5832*(4:ℝ)^(Fintype.card ι)*(M:ℝ)*(B:ℝ)^3)*(M:ℝ)^2 := by
    calc
      _ = ((Nat.card (BadPoints B p κ T):ℝ)*(M:ℝ)^2)*T^3 := by ring
      _ ≤ ((Nat.card (Exceptional p κ T):ℝ)*(27*(B:ℝ)^3))*T^3 :=
        mul_le_mul_of_nonneg_right hpnt (pow_nonneg hT.le 3)
      _ = ((Nat.card (Exceptional p κ T):ℝ)*T^3)*(27*(B:ℝ)^3) := by ring
      _ ≤ (216*(4:ℝ)^(Fintype.card ι)*(M:ℝ)^3)*(27*(B:ℝ)^3) :=
        mul_le_mul_of_nonneg_right hfamily (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_right (sq_pos_of_pos hM)).mp hscaled

end OriginalBadLatticePointTail318
