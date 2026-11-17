module
public import OriginalFiniteSieveUnion318
public section
noncomputable section
namespace OriginalSmallPrimeRectangleTail318
open scoped BigOperators
open TernaryQuadraticLineCover318 TernaryCongruenceLattices318
open LiteralAdjacentNormSlice318 OriginalWholeBasisCoordinates318 OriginalReducedResidueBounds318
open OriginalAnisotropicResidueFibers318 OriginalControlledIntegralBasis318
open OriginalFiniteSieveUnion318
set_option maxHeartbeats 5000000

@[expose] def integerObstruction (side : Bool) (κ t : ℤ) (u v z c : Vector ℤ) (p : ℕ) : Prop :=
  (p:ℤ)∣(if side then P' κ t (synthesis u v z c) else P κ t (synthesis u v z c)) ∧
    (p:ℤ)∣D t (synthesis u v z c)

lemma obstruction_reduction (side : Bool) (κ t : ℤ) (u v z c : Vector ℤ)
    (p : ℕ) [Fact p.Prime] :
    integerObstruction side κ t u v z c p ↔ reduce p c∈
      (if side then reducedSecond p κ t u v z else reducedFirst p κ t u v z) := by
  have hP : (P κ t (synthesis u v z c):ZMod p)=P (κ:ZMod p) (t:ZMod p)
      (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) (reduce p c)) := by
    rw [←reduction_synthesis]
    simp [P,reduce]
  have hP' : (P' κ t (synthesis u v z c):ZMod p)=P' (κ:ZMod p) (t:ZMod p)
      (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) (reduce p c)) := by
    rw [←reduction_synthesis]
    simp [P',reduce]
  have hD : (D t (synthesis u v z c):ZMod p)=D (t:ZMod p)
      (fieldSynthesis (reduce p u) (reduce p v) (reduce p z) (reduce p c)) := by
    rw [←reduction_synthesis]
    simp [D,reduce]
  cases side <;> simp only [integerObstruction,Bool.false_eq_true,ite_false,ite_true,
    reducedFirst,reducedSecond,Finset.mem_filter,Finset.mem_univ,true_and,
    ←ZMod.intCast_zmod_eq_zero_iff_dvd,hP,hP',hD]

lemma obstruction_card (side : Bool) (κ t : ℤ) (u v z : Vector ℤ)
    (p : ℕ) [Fact p.Prime] (A B C : ℕ) :
    Nat.card {c : Rectangle A B C // integerObstruction side κ t u v z (coordinates c) p}=
      Nat.card (ResidueRectangle A B C p
        (if side then reducedSecond p κ t u v z else reducedFirst p κ t u v z)) := by
  let e : {c : Rectangle A B C // integerObstruction side κ t u v z (coordinates c) p} ≃
      ResidueRectangle A B C p
        (if side then reducedSecond p κ t u v z else reducedFirst p κ t u v z) :=
    { toFun := fun c => ⟨c.1,(obstruction_reduction side κ t u v z (coordinates c.1) p).mp c.2⟩
      invFun := fun c => ⟨c.1,(obstruction_reduction side κ t u v z (coordinates c.1) p).mpr c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

/-- If p fits inside every rectangle side, all boundary factors are
absorbed WITHOUT discarding them: actual obstruction count*p²<=216ABC. -/
theorem scaled_obstruction_count (side : Bool) (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ label) κ s u v z)
    (p : ℕ) [Fact p.Prime] (hκ : ¬(p:ℤ)∣κ) (ht : ¬(p:ℤ)∣label)
    (A B C : ℕ) (hpA : p≤A) (hpB : p≤B) (hpC : p≤C) :
    Nat.card {c : Rectangle A B C // integerObstruction side κ label u v z (coordinates c) p}*p^2≤
      216*A*B*C := by
  have hpair := original_slice_rectangle_bounds κ label s u v z hb p hκ ht A B C
  have hc : Nat.card {c : Rectangle A B C // integerObstruction side κ label u v z (coordinates c) p}≤
      8*p*(2*A/p+1)*(2*B/p+1)*(2*C/p+1) := by
    rw [obstruction_card]
    cases side
    · exact hpair.1
    · exact hpair.2
  have ha := TriangularLatticeBoxCount318.interval_scaled A p hpA
  have hbb := TriangularLatticeBoxCount318.interval_scaled B p hpB
  have hcc := TriangularLatticeBoxCount318.interval_scaled C p hpC
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul ha hbb) hcc
  calc
    _ ≤ (8*p*(2*A/p+1)*(2*B/p+1)*(2*C/p+1))*p^2 := Nat.mul_le_mul_right _ hc
    _ = 8*(((2*A/p+1)*p)*((2*B/p+1)*p)*((2*C/p+1)*p)) := by ring
    _ ≤ 8*((3*A)*(3*B)*(3*C)) := Nat.mul_le_mul_left 8 hprod
    _ = _ := by ring

/-- Genuine finite low-prime tail for BOTH original reduced coprime
pairs: the obstruction union has mass<=216ABC/Y for Y<p<=min(A,B,C).
The bound is constructed from actual residues, integer fibers, overlap-
safe union and finite telescoping; no prime-distribution theorem is used. -/
theorem actual_small_prime_tail (side : Bool) (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ label) κ s u v z)
    (A B C Y : ℕ) (hY : 0<Y) (S : Finset ℕ)
    (hprime : ∀ p∈S, p.Prime) (hκ : ∀ p∈S, ¬(p:ℤ)∣κ)
    (ht : ∀ p∈S, ¬(p:ℤ)∣label) (hcut : ∀ p∈S, Y<p)
    (hsize : ∀ p∈S, p≤A ∧ p≤B ∧ p≤C) :
    (Nat.card {c : Rectangle A B C // ∃ p : ↥S,
      integerObstruction side κ label u v z (coordinates c) p.1}:ℝ)≤
      216*(A:ℝ)*(B:ℝ)*(C:ℝ)/(Y:ℝ) := by
  apply finite_small_prime_tail S
    (fun p c => integerObstruction side κ label u v z (coordinates c) p.1) Y hY hcut
    (216*(A:ℝ)*(B:ℝ)*(C:ℝ)) (by positivity)
  intro p
  letI : Fact p.1.Prime := ⟨hprime p.1 p.2⟩
  have hsz := hsize p.1 p.2
  have hc := scaled_obstruction_count side κ label s u v z hb p.1 (hκ p.1 p.2) (ht p.1 p.2)
    A B C hsz.1 hsz.2.1 hsz.2.2
  have hpR : (0:ℝ)<p.1 := by exact_mod_cast (hprime p.1 p.2).pos
  apply (le_div_iff₀ (sq_pos_of_pos hpR)).mpr
  exact_mod_cast hc

end OriginalSmallPrimeRectangleTail318
