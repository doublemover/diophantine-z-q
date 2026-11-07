module
public import ActualDoubleQuotient318
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.EllipticCurve
public section
namespace ActualMordellWeil318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine ActualDoubleQuotient318
set_option maxHeartbeats 0
noncomputable section

instance numberField : NumberField K := {}
instance elliptic : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr RootPointAlgebra318.discriminant_nonzero⟩

/-- Finite generation of the actual elliptic-curve group follows from the
proved finite quotient by2 and Mathlib's number-field height descent. -/
theorem finitely_generated : AddGroup.FG E.Point := by
  obtain ⟨C,hC⟩:=approx_parallelogram_law E
  exact AddCommGroup.fg_of_descent' (h:=Point.naiveHeight) doubles_finiteIndex
    (fun P=>by rw [P.naiveHeight_eq_logHeight]; exact Height.logHeight_nonneg P.xRep) hC

/-- Finiteness of the actual torsion subgroup, independently of the later
explicit canonical-height bounds. -/
theorem torsion_finite : Finite (AddCommGroup.torsion E.Point) := finite_torsion

end
end ActualMordellWeil318
#print axioms ActualMordellWeil318.finitely_generated
#print axioms ActualMordellWeil318.torsion_finite
