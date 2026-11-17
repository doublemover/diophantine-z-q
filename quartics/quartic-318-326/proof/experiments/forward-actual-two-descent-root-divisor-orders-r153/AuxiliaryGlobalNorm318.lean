module
public import SqrtTwoExactNorm318
public section
noncomputable section
namespace AuxiliaryGlobalNorm318
open scoped BigOperators
open SqrtTwoSplitPrime318

private theorem norm_product {ι : Type*} (S : Finset ι) (g : ι → K) :
    (∏ i∈S,g i).norm.natAbs=∏ i∈S,(g i).norm.natAbs := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Zsqrtd.norm_one]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi,Zsqrtd.norm_mul,Int.natAbs_mul,ih]

/-- Construct the first global binary value by multiplying the actual
prime-power norm witnesses, then correcting its sign with norm(1+sqrt2)=-1.
The splitting conditions remain explicit here; the selected-prime route
must produce them rather than assume a global norm or factorization parity. -/
theorem integer_selected_norm (S : Finset ℕ) (α : ℕ → ℕ)
    (hS : ∀ p∈S,p.Prime)
    (hlocal : ∀ p∈S, Even (α p) ∨ IsSquare (2:ZMod p))
    (q : ℕ) (hq : q.Prime) (hsq : IsSquare (2:ZMod q))
    (σ : ℤ) (hσ : σ=1 ∨ σ= -1) :
    ∃ x z : ℤ, x^2-2*z^2=σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ) := by
  classical
  have hchoice : ∀ p : ℕ, ∃ g : K, p∈S → g.norm.natAbs=p^α p := by
    intro p
    by_cases hp : p∈S
    · obtain ⟨g,hg⟩ := SqrtTwoNormSufficiency318.prime_power p (α p) (hS p hp) (hlocal p hp)
      exact ⟨g,fun _ => hg⟩
    · exact ⟨1,fun hm => (hp hm).elim⟩
  choose g hg using hchoice
  obtain ⟨w,hw⟩ := SqrtTwoNormSufficiency318.prime_power q 1 hq (Or.inr hsq)
  have hprod : (∏ p∈S,g p).norm.natAbs=∏ p∈S,p^α p := by
    rw [norm_product]
    exact Finset.prod_congr rfl (fun p hp => hg p hp)
  have habs : ((∏ p∈S,g p)*w).norm.natAbs=
      (σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)).natAbs := by
    rw [Zsqrtd.norm_mul,Int.natAbs_mul,hprod,hw,pow_one]
    rcases hσ with rfl | rfl <;>
      simp only [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_neg,
        Int.natAbs_one, one_mul, mul_one]
  obtain ⟨v,hv⟩ := SqrtTwoExactNorm318.exact_of_absolute
    (σ*((∏ p∈S,p^α p):ℕ)*(q:ℤ)) ((∏ p∈S,g p)*w) habs
  exact ⟨v.re,v.im,by simpa only [Zsqrtd.norm,pow_two,mul_assoc] using hv⟩

end AuxiliaryGlobalNorm318
