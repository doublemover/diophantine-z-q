module
public import IntegralSquareInertia318
public section
noncomputable section
namespace SquareRootInertiaBound318
open NumberField
open scoped NumberField
set_option maxHeartbeats 600000
attribute [-instance] DivisionRing.toRatAlgebra
variable {L : Type*} [Field L] [NumberField L] [Algebra ℚ L]

/-- Once inertia fixes one odd-valuation square root, it fixes every other
integer square root in the same field. The product of two odd-valuation
radicands has even valuation, so the earlier integral normalization applies. -/
theorem fixes_of_fixed_odd_root (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hover : P.under ℤ = Ideal.span {(p : ℤ)})
    (h2 : ¬(p : ℤ) ∣ 2) (b c : ℤ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hco : Odd (padicValInt p c)) (x y : L) (hx : x^2 = (b : L)) (hy : y^2 = (c : L))
    (s : L ≃ₐ[ℚ] L) (hs : s ∈ P.inertia (L ≃ₐ[ℚ] L)) (hsy : s y = y) : s x = x := by
  by_cases he : Even (padicValInt p b)
  · exact IntegralSquareInertia318.inertia_fixes_even_square p P hover h2 b hb he x hx s hs
  · have hbo : Odd (padicValInt p b) := Nat.not_even_iff_odd.mp he
    have hbe : Even (padicValInt p (b*c)) := by
      rw [padicValInt.mul hb hc]
      exact hbo.add_odd hco
    have hxy : (x*y)^2 = ((b*c : ℤ) : L) := by rw [mul_pow, hx, hy, Int.cast_mul]
    have hfix := IntegralSquareInertia318.inertia_fixes_even_square p P hover h2
      (b*c) (mul_ne_zero hb hc) hbe (x*y) hxy s hs
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide)] at hy
      exact hc (by exact_mod_cast hy.symm)
    apply mul_right_cancel₀ hy0
    simpa only [map_mul, hsy] using hfix

end SquareRootInertiaBound318
