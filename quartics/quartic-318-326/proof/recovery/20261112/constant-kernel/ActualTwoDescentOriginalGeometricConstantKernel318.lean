module
public import ActualTwoDescentOriginalConstantLatticeUnits318
public section
noncomputable section
namespace ActualTwoDescentOriginalGeometricConstantKernel318
open AlgebraicGeometry
open ActualTwoDescentOriginalSchemeIntegral318 ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentSemilinearLatticeLiftGroup318 ActualTwoDescentSemilinearLatticeLiftCoefficients318
open ActualTwoDescentOriginalGeometricLatticeLiftGroup318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _
local notation "N" => algebraMap F (AlgebraicClosure F)
/-- Every actual geometric lattice-group kernel element is uniquely
multiplication by a NONZERO CONSTANT in the original algebraic-closure
base. This is derived from full lattice preservation and properness. -/
lemma constant_unit (n : F) (hn : n≠0) (u : Group n hn)
    (hu : projection (data n hn) u=1) :
    ∃! c : (AlgebraicClosure F)ˣ,∀ f : SchemeFunctionField (N n),
      operator (data n hn) u f=
        ActualTwoDescentOriginalConstantLatticeUnits318.baseCoefficient (N n) (c:AlgebraicClosure F)*f := by
  obtain ⟨c,hc,huniq⟩ := ActualTwoDescentOriginalConstantLatticeUnits318.constant_unit (N n)
    (coefficient (data n hn) u) (kernel (data n hn) u hu).2
  refine ⟨c,?_,?_⟩
  · intro f
    rw [(kernel (data n hn) u hu).1,hc]
  · intro d hd
    apply huniq d
    have hh := hd 1
    simpa only [mul_one] using hh.symm

end ActualTwoDescentOriginalGeometricConstantKernel318
