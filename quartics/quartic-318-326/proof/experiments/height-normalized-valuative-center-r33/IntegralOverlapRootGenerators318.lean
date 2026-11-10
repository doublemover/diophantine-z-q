module
public import ThreeRootScaledGenerators318
public section
noncomputable section
namespace IntegralOverlapRootGenerators318
open IntegralSourceBranches318 IntegralInfinityCommonBase318 IntegralInfinityCommonOrder318
open IntegralInfinityOverlapRealization318 IntegralOverlapChartMaps318 ThreeRootCoordinates318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance infinityAlgebra :
    Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra

@[expose] def finiteGenerator (j : Fin 3) : OpenOrder R c 0 :=
  generator (fun i => algebraMap R[X] (OpenBase R c 0)
    (IntegralBranchChart318.other (otherTwist R c 0) (otherContact R 0) i)) j
@[expose] def infinityGenerator (j : Fin 3) : IntegralInfinityChart318.Order R c :=
  generator (fun i => algebraMap R[X] (IntegralInfinityChart318.Base R c)
    (IntegralInfinityChart318.coefficient R c i)) j

theorem finiteBaseChange_generator (j : Fin 3) :
    finiteBaseChange R c (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)=
      generator (finiteParameter R c) j :=
  coefficientMap_generator _ (CommonBase R c) j

theorem infinityBaseChange_generator (j : Fin 3) :
    infinityBaseChange R c
      (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j)=
      generator (infinityParameter R c) j := by
  unfold infinityBaseChange
  rw [AlgEquiv.trans_apply]
  change IntegralReciprocalRootScale318.orderParameterEquiv _ _ _
    (coefficientMap _ (CommonBase R c) (infinityGenerator R c j)) = _
  rw [coefficientMap_generator,ThreeRootScaledGenerators318.parameter_generator]

/-- The original finite-to-infinity overlap equivalence retains the exact
identity y_j=y0*v_j for each one of the three ratio roots. -/
theorem actualOverlap_generator (j : Fin 3) :
    actualOverlapEquiv R c (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)=
      (rootUnit R c:CommonBase R c) •
        (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j) := by
  apply (infinityBaseChange R c).injective
  change infinityBaseChange R c
    ((infinityBaseChange R c).symm
      (IntegralReciprocalRootScale318.orderEquiv _ _ (rootUnit R c)
        (infinityParameter_unit R c) (parameter_identity R c)
        (finiteBaseChange R c (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j)))) = _
  rw [AlgEquiv.apply_symm_apply,finiteBaseChange_generator,
    ThreeRootScaledGenerators318.order_scale,map_smul,infinityBaseChange_generator]

/-- Restriction of every actual infinity ratio root into the original common
order is y0^-1 times its corresponding finite root. All signs and all three
factor indices are explicit. -/
theorem infinityMap_generator (j : Fin 3) :
    IntegralOverlapChartMaps318.infinityMap R c (infinityGenerator R c j)=
      (↑(rootUnit R c)⁻¹:CommonBase R c) •
        (1 ⊗ₜ[OpenBase R c 0] finiteGenerator R c j) := by
  apply (actualOverlapEquiv R c).injective
  change actualOverlapEquiv R c
    ((actualOverlapEquiv R c).symm
      (1 ⊗ₜ[IntegralInfinityChart318.Base R c] infinityGenerator R c j)) = _
  rw [AlgEquiv.apply_symm_apply,map_smul,actualOverlap_generator,smul_smul,
    Units.inv_mul,one_smul]
end IntegralOverlapRootGenerators318
