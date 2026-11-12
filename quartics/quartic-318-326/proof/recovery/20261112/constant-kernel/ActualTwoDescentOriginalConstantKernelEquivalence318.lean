module
public import ActualTwoDescentOriginalGlobalUnitLatticeAction318
public section
noncomputable section
namespace ActualTwoDescentOriginalConstantKernelEquivalence318
open AlgebraicGeometry
open ActualTwoDescentOriginalSchemeIntegral318
open ActualTwoDescentSemilinearLatticeLiftGroup318 ActualTwoDescentSemilinearLatticeLiftCoefficients318
open ActualTwoDescentOriginalGeometricLatticeLiftGroup318
open ActualTwoDescentOriginalGlobalUnitLatticeAction318 ActualTwoDescentOriginalConstantLatticeUnits318
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local instance : DecidableEq (AlgebraicClosure F) := Classical.decEq _
local notation "N" => algebraMap F (AlgebraicClosure F)
abbrev Kernel (n : F) (hn : n≠0) := {u : Group n hn // projection (data n hn) u=1}
/-- ALL base units have genuine elements in the actual kernel. -/
def ofBaseUnit (n : F) (hn : n≠0) (c : (AlgebraicClosure F)ˣ) : Kernel n hn :=
  ⟨ofKernelUnit (data n hn) (baseUnit (N n) c) (base_preserves (N n) c),rfl⟩
lemma coefficient_ofBaseUnit (n : F) (hn : n≠0) (c : (AlgebraicClosure F)ˣ) :
    coefficient (data n hn) (ofBaseUnit n hn c).val=baseUnit (N n) c :=
  ofKernelUnit_coefficient (data n hn) _ _
def scalar (n : F) (hn : n≠0) (u : Kernel n hn) : (AlgebraicClosure F)ˣ :=
  Classical.choose (ActualTwoDescentOriginalConstantLatticeUnits318.constant_unit (N n)
    (coefficient (data n hn) u.val) (kernel (data n hn) u.val u.property).2)
lemma scalar_spec (n : F) (hn : n≠0) (u : Kernel n hn) :
    baseCoefficient (N n) (scalar n hn u:AlgebraicClosure F)=
      (coefficient (data n hn) u.val:SchemeFunctionField (N n)) :=
  (Classical.choose_spec (ActualTwoDescentOriginalConstantLatticeUnits318.constant_unit (N n)
    (coefficient (data n hn) u.val) (kernel (data n hn) u.val u.property).2)).1
/-- Actual bijective classification of the full kernel, not a
cardinality claim or classification of a selected scalar subgroup. -/
def equivalence (n : F) (hn : n≠0) : (AlgebraicClosure F)ˣ ≃ Kernel n hn where
  toFun := ofBaseUnit n hn
  invFun := scalar n hn
  left_inv c := by
    apply Units.ext
    apply (baseCoefficient (N n)).injective
    rw [scalar_spec,coefficient_ofBaseUnit] <;> rfl
  right_inv u := by
    apply Subtype.ext
    apply ActualTwoDescentSemilinearLatticeLiftCoefficients318.ext (data n hn)
    · exact u.property.symm
    · rw [coefficient_ofBaseUnit]
      apply Units.ext
      exact scalar_spec n hn u
/-- Multiplication of base units agrees with the ACTUAL ambient lift
group multiplication; the full kernel bijection respects products. -/
lemma multiply (n : F) (hn : n≠0) (c d : (AlgebraicClosure F)ˣ) :
    (ofBaseUnit n hn (c*d)).val=(ofBaseUnit n hn c).val*(ofBaseUnit n hn d).val := by
  apply ActualTwoDescentSemilinearLatticeLiftCoefficients318.ext (data n hn)
  · change 1=1*1
    exact (one_mul _).symm
  · apply Units.ext
    rw [coefficient_ofBaseUnit,coefficient_product,coefficient_ofBaseUnit,coefficient_ofBaseUnit]
    change baseCoefficient (N n) ((c:AlgebraicClosure F)*(d:AlgebraicClosure F))=
      baseCoefficient (N n) (c:AlgebraicClosure F)*(data n hn).sigma 1
        (baseCoefficient (N n) (d:AlgebraicClosure F))
    rw [(data n hn).sigma_one,map_mul]

end ActualTwoDescentOriginalConstantKernelEquivalence318
