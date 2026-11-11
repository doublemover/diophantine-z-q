module
public import ActualGaussianIntegerFibers318
public section
noncomputable section
namespace ActualGaussianSmallPrimeTail318
open scoped BigOperators
open TernaryQuadraticLineCover318 OriginalControlledIntegralBasis318
open OriginalAnisotropicResidueFibers318 OriginalSmallPrimeRectangleTail318
open OriginalFiniteSieveUnion318 OriginalReducedResidueBounds318
open ActualGaussianIntegerFibers318
open OriginalDoubledSmallPrimeTail318 (interval_scaled)
set_option maxHeartbeats 6500000

/-- If p fits inside the FULL width of every rectangle side, all boundary factors are
absorbed WITHOUT discarding them: actual obstruction count*p²<=512ABC. -/
theorem actual_scaled_count (side : Bool) (κ label : ℤ)
    (s : ∀ i : LiteralSliceModulus318.PrimeIndex κ label,
      Option (ZMod (LiteralSliceModulus318.prime κ label i)))
    (u v z : Vector ℤ)
    (hb : IntegralBasisTriple (LiteralSliceModulus318.prime κ label) κ s u v z)
    (p : ℕ) [Fact p.Prime] (hκ : ¬(p:ℤ)∣κ) (ht : ¬(p:ℤ)∣label)
    (A B C : ℕ) (hpA : p≤2*A) (hpB : p≤2*B) (hpC : p≤2*C) :
    Nat.card {c : Rectangle A B C // integerActual side κ label u v z (coordinates c) p}*p^2≤
      512*A*B*C := by
  have hc := rectangle_bound side κ label s u v z hb p hκ ht A B C
  have ha := interval_scaled A p hpA
  have hbb := interval_scaled B p hpB
  have hcc := interval_scaled C p hpC
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul ha hbb) hcc
  calc
    _ ≤ (8*p*(2*A/p+1)*(2*B/p+1)*(2*C/p+1))*p^2 := Nat.mul_le_mul_right _ hc
    _ = 8*(((2*A/p+1)*p)*((2*B/p+1)*p)*((2*C/p+1)*p)) := by ring
    _ ≤ 8*((4*A)*(4*B)*(4*C)) := Nat.mul_le_mul_left 8 hprod
    _ = _ := by ring

/-- Genuine finite low-prime tail for BOTH actual original Gaussian
pairs P/K and P'/K: the obstruction union has mass<=512ABC/Y for Y<p<=2*min(A,B,C).
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
    (hsize : ∀ p∈S, p≤2*A ∧ p≤2*B ∧ p≤2*C) :
    (Nat.card {c : Rectangle A B C // ∃ p : ↥S,
      integerActual side κ label u v z (coordinates c) p.1}:ℝ)≤
      512*(A:ℝ)*(B:ℝ)*(C:ℝ)/(Y:ℝ) := by
  apply finite_small_prime_tail S
    (fun p c => integerActual side κ label u v z (coordinates c) p.1) Y hY hcut
    (512*(A:ℝ)*(B:ℝ)*(C:ℝ)) (by positivity)
  intro p
  letI : Fact p.1.Prime := ⟨hprime p.1 p.2⟩
  have hsz := hsize p.1 p.2
  have hc := actual_scaled_count side κ label s u v z hb p.1 (hκ p.1 p.2) (ht p.1 p.2)
    A B C hsz.1 hsz.2.1 hsz.2.2
  have hpR : (0:ℝ)<p.1 := by exact_mod_cast (hprime p.1 p.2).pos
  apply (le_div_iff₀ (sq_pos_of_pos hpR)).mpr
  exact_mod_cast hc

end ActualGaussianSmallPrimeTail318
