module
public import ActualTZJointPrimeDensity318
public import ActualTZBooleanPrimeSlots318
import all ActualTZJointPrimeDensity318
public section
noncomputable section
namespace ActualTZChoiceJointDensity318
open scoped BigOperators
open ActualTZBooleanPrimeSlots318 ActualTZJointPrimeDensity318
open ActualTZRegulatedPhysicalPrime318 ActualTZMultiLinearCRT318

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem true_pick (P : ℕ) (x : Choices I P) (p : PrimeAt P) :
    pickPrime (digit P x) p.val true=(x p).1 := by
  funext i
  have H := (pickPrime_true (digit P x) p.val true i).trans (digit_iff_bit P x p (i,true))
  cases h₁ : pickPrime (digit P x) p.val true i <;> cases h₂ : (x p).1 i <;>
    simp_all [bit]

theorem false_pick (P : ℕ) (x : Choices I P) (p : PrimeAt P) :
    pickPrime (digit P x) p.val false=(x p).2 := by
  funext i
  have H := (pickPrime_true (digit P x) p.val false i).trans (digit_iff_bit P x p (i,false))
  cases h₁ : pickPrime (digit P x) p.val false i <;> cases h₂ : (x p).2 i <;>
    simp_all [bit]

def localChoice (W P : ℕ) (a : I→ℤ) (b : I→ℕ) (x : Choices I P) (p : PrimeAt P) : ℂ :=
  let hp := Nat.prime_of_mem_primesBelow p.property
  letI : NeZero p.val := ⟨hp.ne_zero⟩
  physicalMass W p.val a b (x p).1 (x p).2

/-- Exact density equality on the SAME finite prime assignment. No
extra independent x is used and no cutoff d≤R was inserted yet. -/
theorem density_from_choices (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (x : Choices I P) :
    (jointDensity W (digit P x) (a ∘ Prod.fst) (b ∘ Prod.fst):ℂ)=
      ∏ p : PrimeAt P,localChoice W P a b x p := by
  rw [density_eq_universe_product W a b (digit P x) (digit_squarefree P x) hU P
    (digit_supported P x),←Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  have hp := Nat.prime_of_mem_primesBelow p.property
  rw [massAt,dif_pos hp,true_pick P x p,false_pick P x p] <;> rfl

/-- The global supported class is literally the old common-x Fits
predicate, not a conjunction of independent rational samples. -/
theorem same_x_exists_iff (W P : ℕ) (a : I→ℤ) (b : I→ℕ)
    (hU : ∀ i,W.Coprime (b i)) (x : Choices I P) :
    (∃ t : ℤ,Fits W (digit P x) (a ∘ Prod.fst) (b ∘ Prod.fst) t) ↔
      ∀ p∈support (digit P x),Local W p a b (digit P x) :=
  fits_iff_local W a b (digit P x) (digit_squarefree P x) hU

/-- Exact original cutoff coverage for all squarefree slots at once.
The equality of the numeric slot table follows from the explicit
inverse, not from selecting unrelated witnesses per prime. -/
theorem covers_cutoff (P : ℕ) (R : ℝ) (hP : ⌊R⌋₊<P)
    (d : DigitTable I) (hD : ∀ j,Squarefree (d j)) (hR : ∀ j,d j≤⌊R⌋₊) :
    ∃ x : Choices I P,digit P x=d := by
  let v : ActualTZBooleanPrimeSlots318.Slot I→ActualTZPrimeUniverseDigits318.Supported P :=
    fun j => ⟨d j,hD j,by
      intro p hp
      obtain ⟨hp',hdiv,hn⟩ := Nat.mem_primeFactors.mp hp
      exact Nat.mem_primesBelow.mpr
        ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv).trans_lt ((hR j).trans_lt hP),hp'⟩⟩
  refine ⟨(toDigits P).symm v,?_⟩
  funext j
  exact congrArg (fun e => (e j).val) ((toDigits P).apply_symm_apply v)

end ActualTZChoiceJointDensity318
