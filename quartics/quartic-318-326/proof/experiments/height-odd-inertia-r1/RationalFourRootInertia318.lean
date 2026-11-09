module
public import RationalFourRootSplitting318
public import IntegralSquareInertia318
public import Mathlib.NumberTheory.RamificationInertia.Galois
public section
noncomputable section
namespace RationalFourRootInertia318
open NumberField RationalFourRootFiber318 FourRootOrderSigns318
open scoped NumberField
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (a : Fin 4 → ℚ)
abbrev L := PointField a
abbrev G := L a ≃ₐ[ℚ] L a

/-- Every actual inertia automorphism is trivial when the literal scaled
integer radicands have even p-valuations. The field is unchanged. -/
theorem inertia_eq_bot (d : ℚ) (hd : d ≠ 0) (b : Fin 4 → ℤ)
    (hb : ∀ i, b i ≠ 0) (hab : ∀ i, d^2 * a i = (b i : ℚ))
    (p : ℕ) [Fact p.Prime] (h2 : ¬(p : ℤ) ∣ 2)
    (he : ∀ i, Even (padicValInt p (b i)))
    (P : Ideal (𝓞 (L a))) [P.IsPrime]
    (hover : P.under ℤ = Ideal.span {(p : ℤ)}) :
    P.inertia (G a) = ⊥ := by
  apply le_antisymm _ bot_le
  intro s hs
  change s = 1
  have hroot (i : Fin 4) : s (root a i) = root a i := by
    let x : L a := algebraMap ℚ (L a) d * root a i
    have hx : x^2 = (b i : L a) := by
      dsimp [x]
      rw [mul_pow, root_square, ← map_pow, ← map_mul, hab]
      simp
    have hfix := IntegralSquareInertia318.inertia_fixes_even_square p P hover h2
      (b i) (hb i) (he i) x hx s hs
    have hdL : algebraMap ℚ (L a) d ≠ 0 := by
      simpa only [map_zero] using (algebraMap ℚ (L a)).injective.ne hd
    apply mul_left_cancel₀ hdL
    simpa only [x, map_mul, AlgEquiv.commutes] using hfix
  have hpoint : s.toAlgHom.comp (point a) = point a := by
    apply FourRootSignBaseChange318.hom_ext
    intro i
    exact hroot i
  apply AlgEquiv.ext
  intro y
  obtain ⟨z, rfl⟩ := point_surjective a y
  exact AlgHom.congr_fun hpoint z

end RationalFourRootInertia318
