module
public import SqrtTwoNormSufficiency318
public section
noncomputable section
namespace SqrtTwoExactNorm318
open SqrtTwoSplitPrime318

/-- Multiplication by the explicit element 1+sqrt2 reverses the norm.
This removes the absolute-value ambiguity without a sign hypothesis. -/
theorem exact_of_absolute (n : ℤ) (g : K) (hg : g.norm.natAbs=n.natAbs) :
    ∃ z : K, z.norm=n := by
  rcases Int.natAbs_eq_natAbs_iff.mp hg with h | h
  · exact ⟨g,h⟩
  · refine ⟨(⟨1,1⟩ : K)*g, ?_⟩
    rw [Zsqrtd.norm_mul, h]
    norm_num [Zsqrtd.norm]

/-- Signed integral norm sufficiency, including zero. The same inert-prime
parity condition now produces literal integer coordinates rather than only
an absolute norm. No auxiliary value satisfying this condition is selected. -/
theorem integer_norm (n : ℤ)
    (h : ∀ p : ℕ, p.Prime → ¬IsSquare (2 : ZMod p) →
      Even (n.natAbs.factorization p)) :
    ∃ x z : ℤ, x^2-2*z^2=n := by
  by_cases hn : n=0
  · exact ⟨0,0,by simp [hn]⟩
  obtain ⟨g,hg⟩ := SqrtTwoNormSufficiency318.natural_norm n.natAbs
    (Int.natAbs_ne_zero.mpr hn) h
  obtain ⟨z,hz⟩ := exact_of_absolute n g hg
  refine ⟨z.re,z.im,?_⟩
  simpa only [Zsqrtd.norm, pow_two, mul_assoc] using hz

end SqrtTwoExactNorm318
