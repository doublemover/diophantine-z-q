module
public import NormalizedWholeScalarMaps318
public import FourRootSignBaseChange318
public section
noncomputable section
namespace NormalizedWholeRootMaps318
open Polynomial NormalizedWholeOverlap318 NormalizedReciprocalLaurent318 NormalizedWholeOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)

theorem finite_generator (i : Fin 4) :
    finiteMap R d a (FourRootOrderSigns318.generator (DVRNormalizedFiniteOrder318.coefficient R d a) i)=
      FourRootOrderSigns318.generator (finiteParameter R d a) i := by
  change FourRootSignBaseChange318.coefficientMap
    (DVRNormalizedFiniteOrder318.coefficient R d a) (Laurent R) _=_
  exact FourRootSignBaseChange318.coefficientMap_generator _ _ i

theorem fullOverlap_inverse_generator (i : Fin 4) :
    (fullOverlap R d a).symm (FourRootOrderSigns318.generator (infinityParameter R d a) i)=
      (↑(coordinate R)⁻¹:Laurent R) • FourRootOrderSigns318.generator (finiteParameter R d a) i := by
  apply (fullOverlap R d a).injective
  rw [AlgEquiv.apply_symm_apply,map_smul,fullOverlap_generator,smul_smul,Units.inv_mul,one_smul]

theorem infinity_generator (i : Fin 4) :
    infinityMap R d a (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient R d a) i)=
      (↑(coordinate R)⁻¹:Laurent R) • FourRootOrderSigns318.generator (finiteParameter R d a) i := by
  letI : Algebra R[X] (Laurent R) := (reciprocalMap R).toRingHom.toAlgebra
  change (fullOverlap R d a).symm
    (FourRootSignBaseChange318.coefficientMap
      (DVRNormalizedInfinityOrder318.coefficient R d a) (Laurent R) _) = _
  rw [FourRootSignBaseChange318.coefficientMap_generator]
  exact fullOverlap_inverse_generator R d a i
end NormalizedWholeRootMaps318
