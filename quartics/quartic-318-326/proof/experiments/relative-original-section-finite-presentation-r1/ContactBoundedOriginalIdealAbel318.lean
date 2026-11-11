module
public import ContactBoundedCartierAbelNormalization318
public section
noncomputable section
namespace ContactBoundedOriginalIdealAbel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (N : ℕ)
local notation "b" => ContactOriginalRelativePolynomialCharts318.baseMap R
variable (D : ContactBoundedCartierEquiv318.Data c N b)
/-- The new all-scheme bounded construction specializes to the SAME
previous original ideal-sheaf O(D)/fppf Abel construction on affine bases.
No replacing curve, Jacobian, line or polarization enters this bridge. -/
lemma original_ideal_transformation : ContactBoundedCartierAbel318.transformation c N b D=
    ContactProjectiveIdealAbel318.transformation R c D.val.ideal D.property := rfl
end ContactBoundedOriginalIdealAbel318
