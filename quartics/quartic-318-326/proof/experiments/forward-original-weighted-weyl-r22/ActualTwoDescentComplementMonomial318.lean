module
public import ActualTwoDescentSameActualImages318
public section
noncomputable section
namespace ActualTwoDescentComplementMonomial318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentZeroSumCompletion318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Complementary binary prime products multiply to the LITERAL full
support product. This supplies the actual square multiplier for the
fourth class rather than treating coefficient addition as integer addition. -/
theorem actual_complement_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (b : ι → ZMod 2) :
    monomial p (ones ι+b)*monomial p b=∏ i, p i := by
  rw [monomial,monomial,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  change p i^(1+b i).val*p i^(b i).val=p i
  generalize b i=t
  fin_cases t <;> norm_num

lemma actual_zero_monomial {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) :
    monomial p 0=1 := by simp [monomial]

lemma actual_one_monomial {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℕ) :
    monomial p (ones ι)=∏ i, p i := by simp [monomial,ones]

end ActualTwoDescentComplementMonomial318
