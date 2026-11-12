module
public import ActualTwoDescentOriginalArbitraryLiftNativePullback318
public section
noncomputable section
namespace ActualTwoDescentOriginalGeometricArbitraryNativeLift318
open AlgebraicGeometry CategoryTheory
open ActualTwoDescentOriginalSchemeIntegral318 ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentOriginalTorsionPairing318 ActualTwoDescentFieldGaloisTwoTorsion318
open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentSemilinearLatticeLiftGroup318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _
local notation "N" => algebraMap F (AlgebraicClosure F)
def binary (n : F) (hn : n≠0) (a : ActualTwoDescentOriginalGeometricLatticeLiftGroup318.Group n hn) :
    Lift (ActualTwoDescentOriginalFourGenericLatticeAction318.data (N n) (rational_parameter_ne n hn)) :=
  ⟨(Multiplicative.ofAdd (torsionBinaryEquiv n hn
    (projection (ActualTwoDescentOriginalGeometricLatticeLiftGroup318.data n hn) a).toAdd),a.val.2),a.property⟩
def iso (n : F) (hn : n≠0) (a : ActualTwoDescentOriginalGeometricLatticeLiftGroup318.Group n hn) :
    (Scheme.Modules.pullback
      (ActualTwoDescentOriginalTwoTorsionSchemeAction318.iso n hn
        (projection (ActualTwoDescentOriginalGeometricLatticeLiftGroup318.data n hn) a).toAdd).hom).obj
      (ActualTwoDescentOriginalDoublePoleSheaf318.sheaf (N n)) ≅
        ActualTwoDescentOriginalDoublePoleSheaf318.sheaf (N n) :=
  ActualTwoDescentOriginalArbitraryLiftNativePullback318.iso (N n) (rational_parameter_ne n hn) (binary n hn a)
lemma same_operator (n : F) (hn : n≠0) (a : ActualTwoDescentOriginalGeometricLatticeLiftGroup318.Group n hn)
    (f : SchemeFunctionField (N n)) :
    operator (ActualTwoDescentOriginalFourGenericLatticeAction318.data (N n) (rational_parameter_ne n hn))
      (binary n hn a) f=operator (ActualTwoDescentOriginalGeometricLatticeLiftGroup318.data n hn) a f := rfl

end ActualTwoDescentOriginalGeometricArbitraryNativeLift318
