module
public import ContactOriginalTwistingLine318
public import OriginalClutchedFrameTransition318
public section
noncomputable section
namespace ContactOriginalTwistTransition318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalWholeRestriction318 ContactOriginalTwistingLine318
variable (c : Fin 4 → ℚˣ) (d : ℤ)

/-- The actual twist frames on the entire original overlap recover the
specified original Laurent T^d, with the left-coordinate = T^d times
right-coordinate convention required by positive-twist vanishing. -/
lemma inverse_relation (s : Γ((line c d).object,finiteOpen c ⊓ infinityOpen c)) :
    (OpenLineFrameCoordinates318.frame (line c d).object (finiteOpen c) (finiteFrame c d).symm
      (finiteOpen c ⊓ infinityOpen c) inf_le_left).symm s =
    (OpenLineFrameCoordinates318.frame (line c d).object (infinityOpen c) (infinityFrame c d).symm
      (finiteOpen c ⊓ infinityOpen c) inf_le_right).symm s * scalar c (LaurentPolynomial.T d) :=
  OriginalClutchedFrameTransition318.inverse_relation (finiteOpen c) (infinityOpen c) (transitionUnit c d) s
end ContactOriginalTwistTransition318
