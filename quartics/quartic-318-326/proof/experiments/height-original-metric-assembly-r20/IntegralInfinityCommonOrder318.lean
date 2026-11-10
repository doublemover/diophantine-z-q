module
public import IntegralInfinityCommonBase318
public import Mathlib.RingTheory.Localization.BaseChange
public section
noncomputable section
namespace IntegralInfinityCommonOrder318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance infinityAlgebra :
    Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra
local instance infinityTower :
    IsScalarTower R (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := IntegralInfinityChart318.Base R c)
    (A := CommonBase R c) (fun r => ((infinityBaseMap R c).commutes r).symm)

theorem infinity_parameter_map (j : Fin 3) :
    algebraMap (IntegralInfinityChart318.Base R c) (CommonBase R c)
      (algebraMap R[X] (IntegralInfinityChart318.Base R c)
        (IntegralInfinityChart318.coefficient R c j)) = infinityParameter R c j :=
  infinityBaseMap_polynomial R c _

@[expose] def finiteBaseChange :
    CommonBase R c ⊗[OpenBase R c 0] OpenOrder R c 0 ≃ₐ[CommonBase R c]
      ThreeRootOrder318.Order (finiteParameter R c) :=
  ThreeRootOrder318.baseChange
    (R := OpenBase R c 0)
    (fun j : Fin 3 => algebraMap R[X] (OpenBase R c 0)
      (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) j))
    (CommonBase R c)

@[expose] def infinityBaseChange :
    CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c
      ≃ₐ[CommonBase R c] ThreeRootOrder318.Order (infinityParameter R c) :=
  (ThreeRootOrder318.baseChange _ _).trans
    (IntegralReciprocalRootScale318.orderParameterEquiv _ _ (infinity_parameter_map R c))

/-- On the actual finite overlap obtained by inverting y0, the original
finite chart and original reciprocal infinity chart have isomorphic actual
base-changed orders. Each y_j maps to y0 times the corresponding ratio root.
No comparison of generic fields or ranks substitutes for this algebra map. -/
@[expose] def commonOrderEquiv :
    CommonBase R c ⊗[OpenBase R c 0] OpenOrder R c 0 ≃ₐ[CommonBase R c]
      CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c :=
  (finiteBaseChange R c).trans
    ((IntegralReciprocalRootScale318.orderEquiv (infinityParameter R c) (finiteParameter R c)
      (rootUnit R c) (infinityParameter_unit R c) (parameter_identity R c)).trans
      (infinityBaseChange R c).symm)

theorem infinityCoordinate_unit :
    IsUnit ((infinityBaseMap R c).toRingHom
      (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)) := by
  change IsUnit (infinityBaseMap R c
    (algebraMap R[X] (IntegralInfinityChart318.Base R c) X))
  rw [infinityBaseMap_coordinate]
  exact (reciprocalUnit R c).isUnit

/-- The same base map factors through the actual infinity principal open
u≠0. Establishing its inverse is the remaining coefficient-base gluing step. -/
@[expose] def infinityOverlapMap :
    Localization.Away (algebraMap R[X] (IntegralInfinityChart318.Base R c) X) →ₐ[R]
      CommonBase R c where
  __ := IsLocalization.Away.lift (g := (infinityBaseMap R c).toRingHom)
    (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)
    (infinityCoordinate_unit R c)
  commutes' r := by
    change IsLocalization.Away.lift (g := (infinityBaseMap R c).toRingHom)
      (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)
      (infinityCoordinate_unit R c)
      (algebraMap (IntegralInfinityChart318.Base R c)
        (Localization.Away (algebraMap R[X] (IntegralInfinityChart318.Base R c) X))
        (algebraMap R (IntegralInfinityChart318.Base R c) r)) = _
    rw [IsLocalization.Away.lift_eq]
    exact (infinityBaseMap R c).commutes r

theorem infinityOverlapMap_on_base (a : IntegralInfinityChart318.Base R c) :
    infinityOverlapMap R c
      (algebraMap (IntegralInfinityChart318.Base R c)
        (Localization.Away (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)) a) =
      infinityBaseMap R c a := by
  change IsLocalization.Away.lift (g := (infinityBaseMap R c).toRingHom)
    (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)
    (infinityCoordinate_unit R c)
    (algebraMap (IntegralInfinityChart318.Base R c)
      (Localization.Away (algebraMap R[X] (IntegralInfinityChart318.Base R c) X)) a) = _
  exact IsLocalization.Away.lift_eq _ (infinityCoordinate_unit R c) a

end IntegralInfinityCommonOrder318
