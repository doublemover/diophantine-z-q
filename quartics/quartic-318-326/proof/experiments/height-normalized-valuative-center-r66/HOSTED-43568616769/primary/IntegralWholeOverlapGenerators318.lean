module
public import IntegralOriginalCommonRestriction318
public section
noncomputable section
namespace IntegralWholeOverlapGenerators318
open ThreeRootCoordinates318
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318 IntegralWholeOrderOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type*} [CommRing S]

/-- Signed generator scaling on the full order, with no radicand-unit
hypothesis and hence without deleting the branch points. -/
theorem full_scale (a b : Fin 3 → S) (y : Sˣ) (h : ∀ j,b j=a j*(y:S)^2) (j : Fin 3) :
    UnitScaledQuadraticOrder318.three a b y h (generator b j)=(y:S) • generator a j := by
  fin_cases j <;>
    simp [UnitScaledQuadraticOrder318.three,generator,
      Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
      UnitScaledQuadraticOrder318.equiv_root,←Algebra.smul_def,
      TensorProduct.smul_tmul',TensorProduct.tmul_smul]

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem finite_generator (j : Fin 3) :
    finiteMap R c (generator (finiteCoefficient R c) j)=generator (finiteParameter R c) j :=
  coefficientMap_generator _ (Laurent R) j

/-- The full reciprocal inclusion sends each labeled ratio root to the
inverse pivot times the corresponding full finite root. -/
theorem infinity_generator (j : Fin 3) :
    infinityMap R c (generator (IntegralInfinityChart318.coefficient R c) j)=
      (↑(y R)⁻¹:Laurent R) • generator (finiteParameter R c) j := by
  letI : Algebra (Polynomial R) (Laurent R) := (reciprocalMap R c).toRingHom.toAlgebra
  apply (fullOverlap R c).injective
  change fullOverlap R c ((fullOverlap R c).symm
    (infinityBaseChange R c
      (1 ⊗ₜ[Polynomial R] generator (IntegralInfinityChart318.coefficient R c) j))) = _
  rw [AlgEquiv.apply_symm_apply]
  change coefficientMap _ (Laurent R) (generator _ j)=_
  rw [coefficientMap_generator,map_smul,full_scale,smul_smul,Units.inv_mul,one_smul]
end IntegralWholeOverlapGenerators318
