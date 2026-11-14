module
public import G8Nonvanishing
public import ConcreteQuadraticDomains
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public section
namespace ConcreteG8Domain

/-- The actual rational quadratic field used by the source, with i²=2. -/
abbrev K := QuadraticAlgebra ℚ 2 0

instance sqrtTwoNoRoot : Fact (∀ r : ℚ, r^2 ≠ 2+0*r) := by
  refine ⟨?_⟩
  intro r hr
  have hh := ConcreteQuadraticDomains.two_times_square_ne_one (r/2)
  apply hh
  nlinarith

@[expose] def pair (a b : ℚ) : K := ⟨a,b⟩

@[expose] def i : K := pair 0 1

@[expose] noncomputable def D : K := (3-i)^2

theorem i_square : i^2=2 := by
  ext <;> norm_num [i,pair,pow_two]

theorem pair_product (a b c d : ℚ) :
    pair a b*pair c d=pair (a*c+2*b*d) (a*d+b*c) := by
  ext <;> simp [pair] <;> ring

theorem dimension : Module.finrank ℚ K=2 := QuadraticAlgebra.finrank_eq_two (2:ℚ) 0

theorem G8_nonzero (x : K) : G8Nonvanishing.G8 x ≠ 0 :=
  G8Nonvanishing.G8_nonzero (by rw [dimension]; decide) x

/-- The precise denominator polynomial in the relaxed V0 chart is globally
nonzero for every rational pair f0,f1, without a real-sign assumption. -/
theorem actual_V0_denominator_nonzero (f0 f1 : ℚ) :
    G8Nonvanishing.G8 (D*(pair f0 f1)^2) ≠ 0 := G8_nonzero _

end ConcreteG8Domain
