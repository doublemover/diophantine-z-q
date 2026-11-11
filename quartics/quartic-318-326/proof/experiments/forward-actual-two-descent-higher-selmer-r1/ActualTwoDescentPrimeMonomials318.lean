module
public import ActualTwoDescentSimultaneousProducer318
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public section
noncomputable section
namespace ActualTwoDescentPrimeMonomials318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal positive squarefree representative, not a formal vector. -/
def monomial (p : ι → ℕ) (u : ι → ZMod 2) : ℕ := ∏ i, p i ^ (u i).val

lemma monomial_pos (p : ι → ℕ) [∀ i, Fact (p i).Prime] (u : ι → ZMod 2) :
    0 < monomial p u := by
  apply Finset.prod_pos
  intro i _
  exact pow_pos (Fact.out : (p i).Prime).pos _

lemma actual_valuation_product (q : ℕ) [Fact q.Prime] (s : Finset ι)
    (f : ι → ℕ) (hf : ∀ i, f i ≠ 0) :
    padicValNat q (∏ i ∈ s, f i)=∑ i ∈ s, padicValNat q (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,padicValNat.mul (hf i) (Finset.prod_ne_zero_iff.mpr (fun j _ => hf j)),
      Finset.sum_insert hi,ih]

/-- Each exponent is recovered by the actual prime-adic valuation of the
integer representative. Pairwise distinct primes are indispensable here. -/
theorem actual_monomial_valuation (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (u : ι → ZMod 2) (i : ι) :
    padicValNat (p i) (monomial p u)=(u i).val := by
  rw [monomial,actual_valuation_product]
  · simp_rw [padicValNat.pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [padicValNat_primes (fun he => hji (hd he.symm)),mul_zero]
    · simp
  · intro j
    exact pow_ne_zero _ (Fact.out : (p j).Prime).ne_zero

lemma actual_monomial_valuation_bit (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (u : ι → ZMod 2) (i : ι) :
    ((padicValRat (p i) (monomial p u : ℚ) : ℤ) : ZMod 2)=u i := by
  rw [padicValRat.of_nat,actual_monomial_valuation p hd u i]
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

/-- Distinct exponent vectors cannot be made equal by multiplication by
an actual nonzero rational square. This proves squareclass independence
without postulating an abstract squareclass basis. -/
theorem actual_monomial_squareclass_injective (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (u v : ι → ZMod 2) (r : ℚ) (hr : r ≠ 0)
    (he : (monomial p u : ℚ)=(monomial p v : ℚ)*r^2) : u=v := by
  funext i
  have hv : (monomial p v : ℚ) ≠ 0 := by exact_mod_cast (monomial_pos p v).ne'
  have h := congrArg (fun x : ℚ => (padicValRat (p i) x : ZMod 2)) he
  rw [padicValRat.mul hv (pow_ne_zero 2 hr),padicValRat.pow] at h
  simpa only [Int.cast_add,Int.cast_mul,Int.cast_ofNat,show (2 : ZMod 2)=0 from rfl,
    zero_mul,add_zero,actual_monomial_valuation_bit p hd] using h

end ActualTwoDescentPrimeMonomials318
