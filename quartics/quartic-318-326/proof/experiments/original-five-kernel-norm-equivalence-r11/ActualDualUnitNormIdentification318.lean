module
public import DualUnitNormConstruction318
public section
noncomputable section
namespace ActualDualUnitNormIdentification318
open SquareZeroUnit318 DualUnitFactorization318
universe u v
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
local instance dualAlgebra : Algebra (DualNumber R) (DualNumber S) :=
  OriginalDualAlgebraNormTrace318.actualAlgebra R S
/-- Agreement on EVERY unit of the actual dual algebra, not only the
infinitesimal subgroup. This is the genuine original determinant norm. -/
lemma norm_eq : Units.map (Algebra.norm (DualNumber R)) =
    DualUnitNormConstruction318.norm (Units.map (Algebra.norm R)) (Algebra.trace R S) := by
  apply DualUnitNormConstruction318.unique
  · intro a
    apply Units.ext
    exact OriginalDualAlgebraNormTrace318.norm_inl R S a.val
  · intro a
    exact OriginalDualAlgebraNormTrace318.norm_unit R S a
end ActualDualUnitNormIdentification318
