module
public import TriangularLatticeBoxCount318
public section
noncomputable section
namespace OriginalTernaryBoxCount318
open TernaryQuadraticLineCover318 TernaryChartModuli318 TriangularTernaryBasis318
open TriangularLatticeBoxCount318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def OriginalBox (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :=
  {v : Box B // coordinates v∈SquarefreeTernaryLatticeCover318.lattice p hp κ t}

/-- The actual original lattice, in the original integer-coordinate box. -/
theorem original_lattice_scaled (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (hB : FixedSquarefreeCRT318.modulus p≤B) :
    Nat.card (OriginalBox B p hp κ t)*(FixedSquarefreeCRT318.modulus p)^2≤27*B^3 := by
  classical
  obtain ⟨A,D,hA0,hA,hD0,hD,hcoeff⟩ := original_coefficients p hp hd κ t
  let e : OriginalBox B p hp κ t ≃
      LatticeBox B (finiteModulus p t) (infinityModulus p t) A D := {
    toFun := fun v => ⟨v.1,(OriginalTernaryBasis318.membership_iff p hp hd κ A D t hcoeff _).mp v.2⟩
    invFun := fun v => ⟨v.1,(OriginalTernaryBasis318.membership_iff p hp hd κ A D t hcoeff _).mpr v.2⟩
    left_inv := fun v => rfl
    right_inv := fun v => rfl }
  obtain ⟨hq,hr⟩ := moduli_positive p hp t
  have hB' : finiteModulus p t*infinityModulus p t≤B := by rwa [moduli_product]
  have hh := scaled_count B (finiteModulus p t) (infinityModulus p t) hq hr hB' A D
  rw [moduli_product,←Nat.card_congr e] at hh
  exact hh

@[expose] def DivisorBox (B : ℕ) (p : ι → ℕ) (κ : ℤ) :=
  {v : Box B // (FixedSquarefreeCRT318.modulus p:ℤ)∣
    κ*(coordinates v).2.2^2-2*(coordinates v).1*(coordinates v).2.1}

/-- Encode the actual original congruence points into a covering lattice
and that SAME point. Overlaps do not invalidate this injection. -/
@[expose] def encode (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (κ : ℤ) (hp2 : ∀ i, p i≠2) (hκ : ∀ i, ¬(p i:ℤ)∣κ) :
    DivisorBox B p κ → (Σ t : ∀ i, Option (ZMod (p i)), OriginalBox B p hp κ t) := by
  classical
  intro v
  have hh := (SquarefreeTernaryLatticeCover318.divisor_iff_lattice p hp hd κ hp2 hκ (coordinates v.1)).mp v.2
  exact ⟨hh.choose,⟨v.1,hh.choose_spec⟩⟩

lemma encode_injective (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hd : Function.Injective p)
    (κ : ℤ) (hp2 : ∀ i, p i≠2) (hκ : ∀ i, ¬(p i:ℤ)∣κ) :
    Function.Injective (encode B p hp hd κ hp2 hκ) := by
  intro v w he
  apply Subtype.ext
  exact congrArg (fun z : Σ t : ∀ i, Option (ZMod (p i)), OriginalBox B p hp κ t => z.2.1) he

/-- Constructed unweighted congruence count for the full original ternary
polynomial in its original box. This is stronger than assuming a count for
an unspecified family of index-q² lattices. -/
theorem original_congruence_scaled (B : ℕ) (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (κ : ℤ) (hp2 : ∀ i, p i≠2) (hκ : ∀ i, ¬(p i:ℤ)∣κ)
    (hB : FixedSquarefreeCRT318.modulus p≤B) :
    Nat.card (DivisorBox B p κ)*FixedSquarefreeCRT318.modulus p≤
      27*2^(Fintype.card ι)*B^3 := by
  classical
  letI : ∀ i, NeZero (p i) := fun i => ⟨(hp i).ne_zero⟩
  have hcard : Nat.card (DivisorBox B p κ)≤
      ∑ t : ∀ i, Option (ZMod (p i)), Nat.card (OriginalBox B p hp κ t) := by
    have hh := Nat.card_le_card_of_injective (encode B p hp hd κ hp2 hκ)
      (encode_injective B p hp hd κ hp2 hκ)
    simpa only [Nat.card_eq_fintype_card,Fintype.card_sigma] using hh
  have hs : Nat.card (DivisorBox B p κ)*(FixedSquarefreeCRT318.modulus p)^2≤
      Nat.card (∀ i, Option (ZMod (p i)))*(27*B^3) := by
    calc
      Nat.card (DivisorBox B p κ)*(FixedSquarefreeCRT318.modulus p)^2≤
        (∑ t : ∀ i, Option (ZMod (p i)), Nat.card (OriginalBox B p hp κ t))*
          (FixedSquarefreeCRT318.modulus p)^2 := Nat.mul_le_mul_right _ hcard
      _ = ∑ t : ∀ i, Option (ZMod (p i)), Nat.card (OriginalBox B p hp κ t)*
          (FixedSquarefreeCRT318.modulus p)^2 := Finset.sum_mul _ _ _
      _ ≤ ∑ _t : ∀ i, Option (ZMod (p i)), 27*B^3 := by
        apply Finset.sum_le_sum
        intro t ht
        exact original_lattice_scaled B p hp hd κ t hB
      _ = Nat.card (∀ i, Option (ZMod (p i)))*(27*B^3) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hb := hs.trans (Nat.mul_le_mul_right (27*B^3)
    (SquarefreeTernaryLatticeCover318.parameter_bound p hp))
  have hc : (Nat.card (DivisorBox B p κ)*FixedSquarefreeCRT318.modulus p)*
      FixedSquarefreeCRT318.modulus p≤(27*2^(Fintype.card ι)*B^3)*FixedSquarefreeCRT318.modulus p := by
    convert hb using 1 <;> ring
  exact (mul_le_mul_right (FixedSquarefreeCRT318.modulus_positive p hp)).mp hc

end OriginalTernaryBoxCount318
