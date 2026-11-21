module
public import ActualTZSignedPrimeSlotWeight318
public import ActualTZMellinFiniteGuard318
import all ActualTZMellinFiniteGuard318
import all ActualTZLiteralAbsoluteEuler318
public section
noncomputable section
namespace ActualTZFiniteChoiceIntegrand318
open scoped BigOperators
open ActualTZBooleanPrimeSlots318 ActualTZSignedPrimeSlotWeight318
open ActualTZMellinFiniteGuard318 ActualTZMellinKernel318 ActualTZLiteralSchwartz318
open ActualTZLiteralMellinTensor318 (rowProduct spectral)

variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem digit_injective (P : ℕ) :
    Function.Injective (digit P : Choices I P→(Slot I→ℕ)) := by
  intro x y h
  apply (toDigits P).injective
  funext j
  apply Subtype.ext
  exact congrFun h j

def digitTable (I : Type*) [Fintype I] [DecidableEq I] (P : ℕ) :
    Finset (Slot I→ℕ) := Finset.univ.image (digit P : Choices I P→(Slot I→ℕ))

theorem table_pos (P : ℕ) (d : Slot I→ℕ) (hd : d∈digitTable I P) :
    ∀ j,0<d j := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hd
  exact fun j => Nat.pos_of_ne_zero (digit_squarefree P x j).ne_zero

theorem table_squarefree (P : ℕ) (d : Slot I→ℕ) (hd : d∈digitTable I P) :
    ∀ j,Squarefree (d j) := by
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hd
  exact digit_squarefree P x

private theorem exponent_eq (L : ℝ) (ξ : Slot I→ℝ) (j : Slot I) :
    exponent (s1 L ξ) (s2 L ξ) j=mode (ξ j)/(L:ℂ) := by
  rcases j with ⟨i,b⟩
  cases b <;> rfl

private theorem integrand_term (C : Cutoff) (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (L : ℝ) (ξ : Slot I→ℝ) (x : Choices I P) :
    (∏ j : Slot I,φ C (ξ j)) *
      ActualTZLiteralAbsoluteEuler318.choiceWeight W P a b (s1 L ξ) (s2 L ξ) x =
      crc W a b (digit P x)*rowProduct C L (digit P x) ξ := by
  rw [signed_choice W P a b hU,crc,rowProduct]
  simp only [spectral,Finset.prod_mul_distrib,exponent_eq] <;> ac_rfl

/-- No duplicate weights: the finite table is the image of the
explicit injective map of prime assignments to both divisor slots. -/
theorem choice_integrand (C : Cutoff) (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (L : ℝ) (ξ : Slot I→ℝ) :
    (∏ j : Slot I,φ C (ξ j)) *
      (∑ x : Choices I P,ActualTZLiteralAbsoluteEuler318.choiceWeight W P a b (s1 L ξ) (s2 L ξ) x) =
    ∑ d∈digitTable I P,crc W a b d*rowProduct C L d ξ := by
  classical
  rw [Finset.mul_sum,digitTable,Finset.sum_image (digit_injective P).injOn]
  exact Finset.sum_congr rfl fun x _ => integrand_term C W P a b hU L ξ x

/-- Pointwise signed finite Euler expansion (before the φ multiplier).
The regulator sums use the actual common x-cells, not the absolute sums. -/
theorem signed_prime_product (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (s u : I→ℂ) :
    (∏ p : PrimeAt P,∑ t : ActualTZLiteralAbsoluteEuler318.Pair I,
      ActualTZLiteralAbsoluteEuler318.entry W P a b s u p t) =
      ∑ x : Choices I P,ActualTZLiteralAbsoluteEuler318.choiceWeight W P a b s u x := by
  classical
  unfold ActualTZLiteralAbsoluteEuler318.choiceWeight
  rw [Fintype.prod_sum]

end ActualTZFiniteChoiceIntegrand318
