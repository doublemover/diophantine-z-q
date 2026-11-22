module
public import Mathlib.Tactic
public section

namespace ActualGaussianWeberEvenNormLift318

/-- Both coordinate perturbations by the same even modulus preserve
the norm modulo **twice** that modulus. No Gaussian cyclic group,
cyclotomic pairing or reciprocity is a premise. -/
theorem norm_even_shift (M a b x y : ℤ) (hM : Even M) :
    2*M ∣ ((a+M*x)^2+(b+M*y)^2)-(a^2+b^2) := by
  obtain ⟨k,hk⟩ := hM
  refine ⟨a*x+b*y+k*(x^2+y^2),?_⟩
  rw [hk]
  ring

/-- Exact integer congruence-form endpoint, for the literal two
coordinate congruences at the same input modulus. -/
theorem norm_even_congr (M a b c d : ℤ) (hM : Even M)
    (hR : M ∣ a-c) (hI : M ∣ b-d) :
    2*M ∣ (a^2+b^2)-(c^2+d^2) := by
  obtain ⟨x,hx⟩ := hR
  obtain ⟨y,hy⟩ := hI
  have ha : a=c+M*x := by linear_combination hx
  have hb : b=d+M*y := by linear_combination hy
  rw [ha,hb]
  exact norm_even_shift M c d x y hM

end ActualGaussianWeberEvenNormLift318
