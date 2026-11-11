module
public import PELOriginalCubicAdditionSeparateSections318
public import FiniteSeparateFunctionExpansion318
public section
noncomputable section
namespace PELOriginalCubicAdditionConstants318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCubicAdditionSeparateSections318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- A genuine finite constant double expansion of EVERY actual cubic
addition/difference product in the original complete level-six families.
These are constant coefficients independent of BOTH source variables.
Regular realization of the level-six family on the level-three candidate
is a separate algebraic prerequisite, not assumed by this theorem. -/
theorem exists_constants (r s : Label 3) :
    ∃ C : Label 6 → Label 6 → ℂ, ∀ z a : ComplexVectors,
      value τ hτ 3 r (z+a) * value τ hτ 3 s (z-a) =
        ∑ u : Label 6, ∑ v : Label 6,
          C u v * value τ hτ 6 u z * value τ hτ 6 v a :=
  FiniteSeparateFunctionExpansion318.exists_double_expansion
    (value τ hτ 6) (value τ hτ 6) (original_values_independent τ hτ 6)
    (paired τ hτ r s) (first_span τ hτ r s) (second_span τ hτ r s)

@[expose] def additionConstant (r s : Label 3) : Label 6 → Label 6 → ℂ :=
  (exists_constants τ hτ r s).choose

theorem actual_addition_formula (r s : Label 3) (z a : ComplexVectors) :
    value τ hτ 3 r (z+a) * value τ hτ 3 s (z-a) =
      ∑ u : Label 6, ∑ v : Label 6,
        additionConstant τ hτ r s u v * value τ hτ 6 u z * value τ hτ 6 v a :=
  (exists_constants τ hτ r s).choose_spec z a
end PELOriginalCubicAdditionConstants318
