module
public import ContactOriginalLinearOpenChart318
public import ContactLinearFiberDisjoint318
public section
noncomputable section
namespace ContactLinearOpenChartRange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (a : ℚ)
local notation "l" => ContactOriginalLinearOpenChart318.linearForm a
local notation "h" => ContactOriginalLinearOpenChart318.linearForm_homogeneous a
/-- The actual affine source chart is exactly the complement of the
chosen original rational fiber, as an equality of scheme opens. -/
lemma range : (ContactOriginalLinearOpenChart318.affineInto c l h).opensRange=
    (ContactProjectiveModel318.modelMap c) ⁻¹ᵁ ContactLinearFiberDisjoint318.locus a := by
  rw [ContactOriginalLinearOpenChart318.affineInto,Scheme.Hom.opensRange_comp_of_isIso]
  change (pullback.fst (ContactProjectiveModel318.modelMap c)
    (ContactOriginalLinearOpenChart318.baseInto l h)).opensRange=_
  rw [Scheme.Hom.opensRange_pullbackFst]
  change (ContactProjectiveModel318.modelMap c) ⁻¹ᵁ
    (Proj.awayι (ProjectiveJLine318.grading ℚ) l h (by omega)).opensRange=_
  rw [Proj.opensRange_awayι]
  rfl
end ContactLinearOpenChartRange318
