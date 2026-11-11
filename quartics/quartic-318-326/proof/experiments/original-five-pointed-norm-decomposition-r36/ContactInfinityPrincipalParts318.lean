module
public import PolynomialPrincipalParts318
public import InfinityOpenChart318
public import InfinityFieldCoordinates318
public import Mathlib.Tactic.FieldSimp

public section
noncomputable section
namespace ContactInfinityPrincipalParts318
attribute [-instance] DivisionRing.toRatAlgebra
open Polynomial InfinityFieldCoordinates318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (L c) := (KummerTensorField318.source_raw_field c).toField

/-- The original infinity-localization denominator, not a convenient replacement. -/
abbrev denominator := InfinityOpenChart318.denominator c

/-- Exact coefficient reduction for the denominator used by the actual infinity chart. -/
theorem polynomial_decomposition (P : ℚ[X]) (n m : ℕ) :
    ∃ R S : ℚ[X], R.degree < (n : WithBot ℕ) ∧
      P = R * denominator c ^ m + S * X^n :=
  PolynomialPrincipalParts318.decomposition (denominator c) P
    (InfinityOpenChart318.denominator_at_zero_ne_zero c) n m

theorem denominator_at_u_ne_zero : aeval (u c) (denominator c) ≠ 0 := by
  exact fun h => InfinityOpenChart318.denominator_ne_zero c
    ((polynomial_coordinate_injective c) (by simpa only [map_zero] using h))

/-- The exact original-field principal-part identity: the remainder numerator
has degree below the pole order, while the second denominator is regular at infinity. -/
theorem fraction_decomposition (P : ℚ[X]) (n m : ℕ) :
    ∃ R S : ℚ[X], R.degree < (n : WithBot ℕ) ∧
      aeval (u c) P / ((u c)^n * (aeval (u c) (denominator c))^m) =
        aeval (u c) R / (u c)^n +
          aeval (u c) S / (aeval (u c) (denominator c))^m := by
  obtain ⟨R,S,hR,hP⟩ := polynomial_decomposition c P n m
  refine ⟨R,S,hR,?_⟩
  have he := congrArg (aeval (u c)) hP
  simp only [map_add,map_mul,map_pow,aeval_X] at he
  field_simp [u_ne_zero c,denominator_at_u_ne_zero c]
  linear_combination he

end ContactInfinityPrincipalParts318
