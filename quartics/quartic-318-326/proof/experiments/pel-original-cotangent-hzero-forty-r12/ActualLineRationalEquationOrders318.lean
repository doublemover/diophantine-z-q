module
public import ActualLineRationalEquations318
public import ActualDvrMeromorphicOrder318
public import Mathlib.AlgebraicGeometry.FunctionField
public section
noncomputable section
namespace ActualLineRationalEquationOrders318
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X:Scheme.{u}} [IsIntegral X] (M:X.Modules) {ι:Type u}
    (U:ι→X.Opens) [∀i,Nonempty (U i)]
    (frames:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
variable (reference:ι)(f₀:X.functionField)(hf₀:f₀≠0)
variable (x:X) [IsDiscreteValuationRing (X.presheaf.stalk x)]
local notation "ν" => ActualDvrMeromorphicOrder318.value (X.presheaf.stalk x) X.functionField
/-- A genuine regular overlap unit has valuation zero in the ACTUAL
Scheme stalk. This uses the original generization map to its function
field, not a replacement ring with the same residue points. -/
lemma overlap_unit_value(i j:ι)(hi:x∈U i)(hj:x∈U j):
    ν (ActualLineRationalEquations318.transitionGerm M U frames i j)=0:=by
  let W:X.Opens:=U i⊓U j
  letI:Nonempty W:=⟨⟨x,hi,hj⟩⟩
  let e:=LineFrameTransitions318.scalar M U frames i j W inf_le_left inf_le_right
  have hu:IsUnit (X.presheaf.germ W x ⟨hi,hj⟩ e.val):=
    e.isUnit.map (X.presheaf.germ W x ⟨hi,hj⟩).hom
  have hv:=ActualDvrMeromorphicOrder318.value_unit (X.presheaf.stalk x) X.functionField _ hu
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at hv
  exact hv
/-- The orders of the genuine rational local equations are independent
of the selected original canonical frame at every actual DVR stalk in
the overlap. No comparison with a separately computed divisor is assumed. -/
theorem value_independent(i j:ι)(hi:x∈U i)(hj:x∈U j):
    ν (ActualLineRationalEquations318.equation M U frames reference f₀ i)=
      ν (ActualLineRationalEquations318.equation M U frames reference f₀ j):=by
  have he:ActualLineRationalEquations318.equation M U frames reference f₀ i=
      ActualLineRationalEquations318.transitionGerm M U frames i j*
        ActualLineRationalEquations318.equation M U frames reference f₀ j:=by
    change ActualLineRationalEquations318.transitionGerm M U frames i reference*f₀=
      ActualLineRationalEquations318.transitionGerm M U frames i j*
        (ActualLineRationalEquations318.transitionGerm M U frames j reference*f₀)
    rw [←mul_assoc,ActualLineRationalEquations318.transition_comp]
  rw [he,ν.map_mul,overlap_unit_value M U frames x i j hi hj,zero_add]
theorem order_independent(i j:ι)(hi:x∈U i)(hj:x∈U j):
    ActualDvrMeromorphicOrder318.order (X.presheaf.stalk x) X.functionField
      (ActualLineRationalEquations318.equation M U frames reference f₀ i)=
    ActualDvrMeromorphicOrder318.order (X.presheaf.stalk x) X.functionField
      (ActualLineRationalEquations318.equation M U frames reference f₀ j):=by
  unfold ActualDvrMeromorphicOrder318.order
  rw [value_independent M U frames reference f₀ x i j hi hj]
end ActualLineRationalEquationOrders318
